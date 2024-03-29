(* begin-documentation-node
##########
  Kernel
##########

Developing the Kernel...

end-documentation-node *)

(* begin-package-description
Package Overview
++++++++++++++++

The Kernel package manages:

* Loading the Oberon inner core from the SDcard or the serial line
* Heap Management, Disk Access, Timekeeping, and Trap handling

Package Use
+++++++++++

USAGE:

i:=Kernel.Time();

Kernel.Install(SYSTEM.ADR(Abort), 0);

Kernel.GetSector(secno*29, buf);

end-package-description *)

(* begin-module-short-description
manages memory, block access, system timer, and traps.
end-module-short-description *)

(* begin-module-use-description
Module Kernel handles:

* Memory use by the shared Oberon heap including garbage collection
* Reading and writing to SD Card 512-byte blocks
* Allocating, Deallocating, Reading and Writing 1024-byte sectors on the SD card
* Using the sytem timer and clock
* Setting the trap handler and dispatching traps.

end-module-use-description *)

(* begin-module-develop-description
(*NW/PR  11.4.86 / 27.12.95 / 4.2.2014*)

end-module-develop-description *)

MODULE Kernel;  (*NW/PR  11.4.86 / 27.12.95 / 4.2.2014*)
  IMPORT SYSTEM;

  CONST 
    SectorLength* = 1024;
(*    WarningSize* = 80; *)
    timer = -64; spiData = -48; spiCtrl = -44;
    CARD0 = 1; SPIFAST = 4;
    FSoffset = 80000H; (*256MB in 512-byte blocks*)
    mapsize = 10000H; (*1K sectors, 64MB*)
(*    wbsize = 4096; *)

  TYPE 
    Sector* = ARRAY SectorLength OF BYTE;
(*    Warning* = POINTER TO ARRAY WarningSize OF CHAR; *)

  VAR 
    allocated*, NofSectors*: INTEGER;
    heapOrg*, heapLim*: INTEGER; 
    stackOrg* ,  stackSize*, MemLim*: INTEGER;
    clock: INTEGER;
    list0, list1, list2, list3: INTEGER;  (*lists of free blocks of size n*256, 128, 64, 32 bytes*)
    data: INTEGER; (*SPI data in*)
    sectorMap: ARRAY mapsize DIV 32 OF SET;
(*    warnBuffer: ARRAY wbsize OF CHAR; *)
(*    wbStart, wbEnd: INTEGER;   *)

(*
  (* begin-section-description
## ---------- Error Reporting
  end-section-description *)

  (* begin-procedure-description
---
**WARNING** logs a warning or error condition. 
  end-procedure-description *)
  PROCEDURE WARNING(w: ARRAY OF CHAR);
  BEGIN
  END WARNING;

  (* begin-procedure-description
---
**WARN1** logs the first occurance of a warning or error condition.
  end-procedure-description *)
  PROCEDURE WARN1(w: ARRAY OF CHAR);
  BEGIN
  END WARN1;
*)

  (* begin-section-description
## ---------- Heap Allocation
  end-section-description *)

  (* begin-procedure-description
---
**GetBlock** gets a block from the heap of a regular size. 
  end-procedure-description *)
  PROCEDURE GetBlock(VAR p: LONGINT; len: LONGINT);
    (*len is multiple of 256*)
    VAR q0, q1, q2, size: LONGINT; done: BOOLEAN;
  BEGIN q0 := 0; q1 := list0; done := FALSE;
    WHILE ~done & (q1 # 0) DO
      SYSTEM.GET(q1, size); SYSTEM.GET(q1+8, q2);
      IF size < len THEN (*no fit*) q0 := q1; q1 := q2
      ELSIF size = len THEN (*extract -> p*)
        done := TRUE; p := q1;
        IF q0 # 0 THEN SYSTEM.PUT(q0+8, q2) ELSE list0 := q2 END
      ELSE (*reduce size*)
        done := TRUE; p := q1; q1 := q1 + len;
        SYSTEM.PUT(q1, size-len); SYSTEM.PUT(q1+4, -1); SYSTEM.PUT(q1+8, q2);
        IF q0 # 0 THEN SYSTEM.PUT(q0+8, q1) ELSE list0 := q1 END
      END
    END ;
    IF ~done THEN p := 0 END
  END GetBlock;

  (* begin-procedure-description
---
**GetBlock128** gets a 128-byte block from the heap.
  end-procedure-description *)
  PROCEDURE GetBlock128(VAR p: LONGINT);
    VAR q: LONGINT;
  BEGIN
    IF list1 # 0 THEN p := list1; SYSTEM.GET(list1+8, list1)
    ELSE GetBlock(q, 256); SYSTEM.PUT(q+128, 128); SYSTEM.PUT(q+132, -1); SYSTEM.PUT(q+136, list1);
      list1 := q + 128; p := q
    END
  END GetBlock128;

  (* begin-procedure-description
---
**GetBlock64** gets a 64-byte block from the heap. 
  end-procedure-description *)
  PROCEDURE GetBlock64(VAR p: LONGINT);
    VAR q: LONGINT;
  BEGIN
    IF list2 # 0 THEN p := list2; SYSTEM.GET(list2+8, list2)
    ELSE GetBlock128(q); SYSTEM.PUT(q+64, 64); SYSTEM.PUT(q+68, -1); SYSTEM.PUT(q+72, list2);
      list2 := q + 64; p := q
    END
  END GetBlock64;

  (* begin-procedure-description
---
**GetBlock32** gets a 32-byte block from the heap.
  end-procedure-description *)
  PROCEDURE GetBlock32(VAR p: LONGINT);
    VAR q: LONGINT;
  BEGIN
    IF list3 # 0 THEN p := list3; SYSTEM.GET(list3+8, list3)
    ELSE GetBlock64(q); SYSTEM.PUT(q+32, 32); SYSTEM.PUT(q+36, -1); SYSTEM.PUT(q+40, list3);
      list3 := q + 32; p := q
    END
  END GetBlock32;

  (* begin-procedure-description
---
**New** gets an appropriate block from the heap to hold a new object and initializes it to zero. 
  end-procedure-description *)
   PROCEDURE New*(VAR ptr: LONGINT; tag: LONGINT);
    (*called by NEW via MT[0]; ptr and tag are pointers*)
    VAR p, size, lim: LONGINT;
  BEGIN SYSTEM.GET(tag, size);
    IF size = 32 THEN GetBlock32(p)
    ELSIF size = 64 THEN GetBlock64(p)
    ELSIF size = 128 THEN GetBlock128(p)
    ELSE GetBlock(p, (size+255) DIV 256 * 256)
    END ;
    IF p = 0 THEN ptr := 0
    ELSE ptr := p+8; SYSTEM.PUT(p, tag); lim := p + size; INC(p, 4); INC(allocated, size);
      WHILE p < lim DO SYSTEM.PUT(p, 0); INC(p, 4) END
    END
  END New;

  (* begin-procedure-description
---
**Interface** allocates and initializes an interface method table for a referenced record with type-bound procedures. 
  end-procedure-description *)
   PROCEDURE Interface*(VAR ptr: LONGINT; tag: LONGINT);
    (*called by assignment of record to interface via MT[0]; ptr and tag are pointers*)
    VAR p, size, lim: LONGINT;
  BEGIN SYSTEM.GET(tag, size);   (* this is all wrong. Need to replace with correct code. *)
    IF size = 32 THEN GetBlock32(p)
    ELSIF size = 64 THEN GetBlock64(p)
    ELSIF size = 128 THEN GetBlock128(p)
    ELSE GetBlock(p, (size+255) DIV 256 * 256)
    END ;
    IF p = 0 THEN ptr := 0
    ELSE ptr := p+8; SYSTEM.PUT(p, tag); lim := p + size; INC(p, 4); INC(allocated, size);
      WHILE p < lim DO SYSTEM.PUT(p, 0); INC(p, 4) END
    END
  END Interface;

  (* begin-section-description
## ---------- Garbage Collection
  end-section-description *)

  (* begin-procedure-description
---
**Mark** traverses the heap from roots, identifying live objects. 
  end-procedure-description *)
  PROCEDURE Mark*(pref: LONGINT);
    VAR pvadr, offadr, offset, tag, p, q, r: LONGINT;
  BEGIN SYSTEM.GET(pref, pvadr); (*pointers < heapOrg considered NIL*)
    WHILE pvadr # 0 DO
      SYSTEM.GET(pvadr, p); SYSTEM.GET(p-4, offadr);
      IF (p >= heapOrg) & (offadr = 0) THEN q := p;   (*mark elements in data structure with root p*)
        REPEAT SYSTEM.GET(p-4, offadr);
          IF offadr = 0 THEN SYSTEM.GET(p-8, tag); offadr := tag + 16 ELSE INC(offadr, 4) END ;
          SYSTEM.PUT(p-4, offadr); SYSTEM.GET(offadr, offset);
          IF offset # -1 THEN (*down*)
            SYSTEM.GET(p+offset, r); SYSTEM.GET(r-4, offadr);
            IF (r >= heapOrg) & (offadr = 0) THEN SYSTEM.PUT(p+offset, q); q := p; p := r END
          ELSE (*up*) SYSTEM.GET(q-4, offadr); SYSTEM.GET(offadr, offset);
            IF p # q THEN SYSTEM.GET(q+offset, r); SYSTEM.PUT(q+offset, p); p := q; q := r END
          END
        UNTIL (p = q) & (offset = -1)
      END ;
      INC(pref, 4); SYSTEM.GET(pref, pvadr)
    END
  END Mark;

  (* begin-procedure-description
---
**Scan** traverses the heap de-allocating unreachable objects. 
  end-procedure-description *)
  PROCEDURE Scan*;
    VAR p, q, mark, tag, size: LONGINT;
  BEGIN p := heapOrg;
    REPEAT SYSTEM.GET(p+4, mark); q := p;
      WHILE mark = 0 DO
        SYSTEM.GET(p, tag); SYSTEM.GET(tag, size); INC(p, size); SYSTEM.GET(p+4, mark)
      END ;
      size := p - q; DEC(allocated, size);  (*size of free block*)
      IF size > 0 THEN
        IF size MOD 64 # 0 THEN
          SYSTEM.PUT(q, 32); SYSTEM.PUT(q+4, -1); SYSTEM.PUT(q+8, list3); list3 := q; INC(q, 32); DEC(size, 32)
        END ;
        IF size MOD 128 # 0 THEN
          SYSTEM.PUT(q, 64); SYSTEM.PUT(q+4, -1); SYSTEM.PUT(q+8, list2); list2 := q; INC(q, 64); DEC(size, 64)
        END ;
        IF size MOD 256 # 0 THEN
          SYSTEM.PUT(q, 128); SYSTEM.PUT(q+4, -1); SYSTEM.PUT(q+8,  list1); list1 := q; INC(q, 128); DEC(size, 128)
        END ;
        IF size > 0 THEN
          SYSTEM.PUT(q, size); SYSTEM.PUT(q+4, -1); SYSTEM.PUT(q+8, list0); list0 := q; INC(q, size)
        END
      END ;
      IF mark > 0 THEN SYSTEM.GET(p, tag); SYSTEM.GET(tag, size); SYSTEM.PUT(p+4, 0); INC(p, size)
      ELSE (*free*) SYSTEM.GET(p, size); INC(p, size)
      END
    UNTIL p >= heapLim
  END Scan;

  (* begin-section-description
## ---------- SPI Block Operations (see also BootLoad.Mod for the same procedures)
  end-section-description *)

  (* begin-procedure-description
---
**SPIIdle** 
  end-procedure-description *)
  PROCEDURE SPIIdle(n: INTEGER); (*send n FFs slowly with no card selected*)
  BEGIN SYSTEM.PUT(spiCtrl, 0);
    WHILE n > 0 DO DEC(n); SYSTEM.PUT(spiData, -1);
      REPEAT UNTIL SYSTEM.BIT(spiCtrl, 0);
      SYSTEM.GET(spiData, data)
    END
  END SPIIdle;

  (* begin-procedure-description
---
**SPI** 
  end-procedure-description *)
  PROCEDURE SPI(n: INTEGER); (*send&rcv byte slowly with card selected*)
  BEGIN SYSTEM.PUT(spiCtrl, CARD0); SYSTEM.PUT(spiData, n);
    REPEAT UNTIL SYSTEM.BIT(spiCtrl, 0);
    SYSTEM.GET(spiData, data)
  END SPI;

  (* begin-procedure-description
---
**SPICmd** 
  end-procedure-description *)
  PROCEDURE SPICmd(n, arg: INTEGER);
    VAR i, crc: INTEGER;
  BEGIN (*send cmd*)
    REPEAT SPIIdle(1) UNTIL data = 255; (*flush while unselected*)
    REPEAT SPI(255) UNTIL data = 255; (*flush while selected*)
    IF n = 8 THEN crc := 135 ELSIF n = 0 THEN crc := 149 ELSE crc := 255 END;
    SPI(n MOD 64 + 64); (*send command*)
    FOR i := 24 TO 0 BY -8 DO SPI(ROR(arg, i)) END; (*send arg*)
    SPI(crc); i := 32;
    REPEAT SPI(255); DEC(i) UNTIL (data < 80H) OR (i = 0)
  END SPICmd;

  (* begin-procedure-description
---
**SDShift** 
  end-procedure-description *)
  PROCEDURE SDShift(VAR n: INTEGER);
    VAR data: INTEGER;
  BEGIN SPICmd(58, 0);  (*CMD58 get card capacity bit*)
    SYSTEM.GET(spiData, data); SPI(-1);
    IF (data # 0) OR ~SYSTEM.BIT(spiData, 6) THEN n := n * 512 END ;  (*non-SDHC card*)
    SPI(-1); SPI(-1); SPIIdle(1)  (*flush response*)
  END SDShift;

  (* begin-procedure-description
---
**ReadSD** 
  end-procedure-description *)
  PROCEDURE ReadSD(src, dst: INTEGER);
    VAR i: INTEGER;
  BEGIN SDShift(src); SPICmd(17, src); ASSERT(data = 0); (*CMD17 read one block*)
    i := 0; (*wait for start data marker*)
    REPEAT SPI(-1); INC(i) UNTIL data = 254;
    SYSTEM.PUT(spiCtrl, SPIFAST + CARD0);
    FOR i := 0 TO 508 BY 4 DO
      SYSTEM.PUT(spiData, -1);
      REPEAT UNTIL SYSTEM.BIT(spiCtrl, 0);
      SYSTEM.GET(spiData, data); SYSTEM.PUT(dst, data); INC(dst, 4)
    END;
    SPI(255); SPI(255); SPIIdle(1) (*may be a checksum; deselect card*)
  END ReadSD;

  (* begin-procedure-description
---
**WriteSD** 
  end-procedure-description *)
  PROCEDURE WriteSD(dst, src: INTEGER);
    VAR i, n: INTEGER; x: BYTE;
  BEGIN SDShift(dst); SPICmd(24, dst); ASSERT(data = 0); (*CMD24 write one block*)
    SPI(254); (*write start data marker*)
    SYSTEM.PUT(spiCtrl, SPIFAST + CARD0);
    FOR i := 0 TO 508 BY 4 DO
      SYSTEM.GET(src, n); INC(src, 4); SYSTEM.PUT(spiData, n);
      REPEAT UNTIL SYSTEM.BIT(spiCtrl, 0)
    END;
    SPI(255); SPI(255); (*dummy checksum*) i := 0;
    REPEAT SPI(-1); INC(i); UNTIL (data MOD 32 = 5) OR (i = 10000);
    ASSERT(data MOD 32 = 5); SPIIdle(1) (*deselect card*)
  END WriteSD;

  (* begin-section-description
## ---------- Disk Sector Operations
  end-section-description *)

  (* begin-procedure-description
---
**InitSecMap** 
  end-procedure-description *)
  PROCEDURE InitSecMap*;
    VAR i: INTEGER;
  BEGIN NofSectors := 0; sectorMap[0] := {0 .. 31}; sectorMap[1] := {0 .. 31};
    FOR i := 2 TO mapsize DIV 32 - 1 DO sectorMap[i] := {} END
  END InitSecMap;

  (* begin-procedure-description
---
**MarkSector** 
  end-procedure-description *)
  PROCEDURE MarkSector*(sec: INTEGER);
  BEGIN sec := sec DIV 29; ASSERT(SYSTEM.H(0) = 0);
    INCL(sectorMap[sec DIV 32], sec MOD 32); INC(NofSectors)
  END MarkSector;

  (* begin-procedure-description
---
**FreeSector** 
  end-procedure-description *)
  PROCEDURE FreeSector*(sec: INTEGER);
  BEGIN sec := sec DIV 29; ASSERT(SYSTEM.H(0) = 0);
    EXCL(sectorMap[sec DIV 32], sec MOD 32); DEC(NofSectors)
  END FreeSector;

  (* begin-procedure-description
---
**AllocSector** 
  end-procedure-description *)
  PROCEDURE AllocSector*(hint: INTEGER; VAR sec: INTEGER);
    VAR s: INTEGER;
  BEGIN (*find free sector, starting after hint*)
    hint := hint DIV 29; ASSERT(SYSTEM.H(0) = 0); s := hint;
    REPEAT INC(s);
      IF s = mapsize THEN s := 1 END ;
    UNTIL ~(s MOD 32 IN sectorMap[s DIV 32]);
    INCL(sectorMap[s DIV 32], s MOD 32); INC(NofSectors); sec := s * 29
  END AllocSector;

  (* begin-procedure-description
---
**GetSector** 
  end-procedure-description *)
  PROCEDURE GetSector*(src: INTEGER; VAR dst: Sector);
  BEGIN src := src DIV 29; ASSERT(SYSTEM.H(0) = 0);
    src := src * 2 + FSoffset;
    ReadSD(src, SYSTEM.ADR(dst)); ReadSD(src+1, SYSTEM.ADR(dst)+512) 
  END GetSector;
  
  (* begin-procedure-description
---
**PutSector** 
  end-procedure-description *)
  PROCEDURE PutSector*(dst: INTEGER; VAR src: Sector);
  BEGIN dst := dst DIV 29; ASSERT(SYSTEM.H(0) =  0);
    dst := dst * 2 + FSoffset;
    WriteSD(dst, SYSTEM.ADR(src)); WriteSD(dst+1, SYSTEM.ADR(src)+512)
  END PutSector;

  (* begin-section-description
## ---------- Time and Clock Operations
  end-section-description *)

  (* begin-procedure-description
---
**Time** gets the current timer value.
  end-procedure-description *)
  PROCEDURE Time*(): INTEGER;
    VAR t: INTEGER;
  BEGIN SYSTEM.GET(timer, t); RETURN t
  END Time;

  (* begin-procedure-description
---
**Clock** gets the current clock value.
  end-procedure-description *)
  PROCEDURE Clock*(): INTEGER;
  BEGIN RETURN clock
  END Clock;

  (* begin-procedure-description
---
**SetClock** sets the clock.
  end-procedure-description *)
  PROCEDURE SetClock*(dt: INTEGER);
  BEGIN clock := dt
  END SetClock;

  (* begin-section-description
## ---------- Trap and Fault Handling
  end-section-description *)

  (* begin-procedure-description
---
**Install** constructs a branch instruction to the specified trap handler and places it.
  end-procedure-description *)
  PROCEDURE Install*(Padr, at: INTEGER);
  BEGIN SYSTEM.PUT(at, 0E7000000H + (Padr - at) DIV 4 -1)
  END Install;

  (* begin-procedure-description
---
**Trap** is a temporary trap handler used in system initialization that either allocates memory (trap 0) or 
emits the trap number on the LEDs and goes into an infinite loop.
  end-procedure-description *)
  PROCEDURE Trap(VAR a: INTEGER; b: INTEGER);
    VAR u, v, w: INTEGER;
  BEGIN u := SYSTEM.REG(15); SYSTEM.GET(u - 4, v); w := v DIV 10H MOD 10H; (*trap number*)
    IF w = 0 THEN New(a, b)
    ELSIF w = 8 THEN Interface(a, b)
    ELSE (*stop*) LED(w + 192); REPEAT UNTIL FALSE
    END
  END Trap;

  (* begin-procedure-description
---
**Init** is called by Modules on system startup to install a temporary trap handler and then initialize memory and the sector map. 
  end-procedure-description *)
  PROCEDURE Init*;
  BEGIN   OUCH(75); OUCH(69);  OUCH(82);  OUCH(78);  OUCH(69);  OUCH(76);  OUCH(10);  
    Install(SYSTEM.ADR(Trap), 20H);  (*install temporary trap*)
    SYSTEM.GET(12, MemLim); SYSTEM.GET(24, heapOrg);
    stackOrg := heapOrg; stackSize := 8000H; heapLim := MemLim;
    list1 := 0; list2 := 0; list3 := 0; list0 := heapOrg;
    SYSTEM.PUT(list0, heapLim - heapOrg); SYSTEM.PUT(list0+4, -1); SYSTEM.PUT(list0+8, 0);
    allocated := 0; clock := 0; InitSecMap
  END Init;

END Kernel.
