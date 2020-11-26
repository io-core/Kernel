(* begin-package-description
### _Package Overview:_
The Kernel package manages:
* Loading the Oberon inner core from the SDcard or the serial line
* Heap Management, Disk Access, Timekeeping, and Trap handling
### _Package Use:_

USAGE:
```
i:=Kernel.Time();

Kernel.Install(SYSTEM.ADR(Abort), 0);

Kernel.GetSector(secno*29, buf);
```

### _Modules in this package:_
end-package-description *)

(* begin-module-use-description
Module Kernel handles:
* Memory use by the shared Oberon heap including garbage collection
* Reading and writing to SD Card 512-byte blocks
* Allocating, Deallocating, Reading and Writing 1024-byte sectors on the SD card
* Using the sytem timer and clock
* Setting the trap handler and dispatching traps.

end-module-use-description *)
MODULE Kernel;  (*NW/PR  11.4.86 / 27.12.95 / 4.2.2014*)
  IMPORT SYSTEM;

  CONST 
    SectorLength* = 1024;
    timer = -64;
    FSoffset = 0H; (*256MB in 512-byte blocks*)
    mapsize = 10000H; (*1K sectors, 64MB*)

  TYPE 
    Sector* = ARRAY SectorLength OF BYTE;

  VAR 
    allocated*, NofSectors*: INTEGER;
    heapOrg*, heapLim*: INTEGER; 
    stackOrg* ,  stackSize*, MemLim*: INTEGER;
    clock, clockTime: INTEGER;
    list0, list1, list2, list3: INTEGER;  (*lists of free blocks of size n*256, 128, 64, 32 bytes*)
    sectorMap: ARRAY mapsize DIV 32 OF SET;

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
**LastUsedSector**
  end-procedure-description *)
  PROCEDURE LastUsedSector*(): INTEGER;
  VAR i, j, secno: INTEGER;
  BEGIN
    i := mapsize DIV 32 - 1;
    WHILE sectorMap[i] = {} DO DEC(i) END;
    FOR j := 0 TO 31 DO
      IF j IN sectorMap[i] THEN secno := i * 32 + j END;
    END;
  RETURN secno * 29
  END LastUsedSector;

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
    src := src + FSoffset DIV 2;
    SYSTEM.PUT(-28, SYSTEM.ADR(dst));
    SYSTEM.PUT(-28, 080000000H + src);
  END GetSector;
  
  (* begin-procedure-description
---
**PutSector** 
  end-procedure-description *)
  PROCEDURE PutSector*(dst: INTEGER; VAR src: Sector);
  BEGIN dst := dst DIV 29; ASSERT(SYSTEM.H(0) =  0);
    dst := dst + FSoffset DIV 2;
    SYSTEM.PUT(-28, SYSTEM.ADR(src));
    SYSTEM.PUT(-28, 0C0000000H + dst);
  END PutSector;

  (* begin-procedure-description
---
**PutSector** 
  end-procedure-description *)
  PROCEDURE TrimAllSectorsAfter*(sec: INTEGER);
  BEGIN sec := sec DIV 29; ASSERT(SYSTEM.H(0) = 0);
    sec := sec + FSoffset DIV 2 + 1;
    SYSTEM.PUT(-28, 3FFFFFFFH);
    SYSTEM.PUT(-28, 0C0000000H + sec);
  END TrimAllSectorsAfter;

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
**AddDays** 
  end-procedure-description *)
  PROCEDURE AddDays(clockPart, days: INTEGER) : INTEGER;
  VAR year, month, day, monthLength : INTEGER;
  BEGIN
    year := clockPart DIV 200H;
    month := clockPart DIV 20H MOD 10H;
    day := clockPart MOD 20H + days;
    REPEAT
      IF month # 2 THEN
        monthLength := 30 + (month + month DIV 8) MOD 2
      ELSIF (year MOD 4 = 0) & ((year MOD 100 # 0) OR (year MOD 400 = 0)) THEN
        monthLength := 29
      ELSE
        monthLength := 28
      END;
      IF day > monthLength THEN
        INC(month); DEC(day, monthLength);
        IF month = 13 THEN INC(year); month := 1 END;
        monthLength := 28 (* will recalculate in next loop run, if required *)
      END
    UNTIL day <= monthLength;
  RETURN (year * 10H + month) * 20H + day
  END AddDays;
  
  (* begin-procedure-description
---
**UpdateClock** 
  end-procedure-description *)
  PROCEDURE UpdateClock;
  VAR value, rest: INTEGER;
  BEGIN
    value := (Time() - clockTime) DIV 1000;
    clockTime := clockTime + value * 1000;
    value := clock MOD 40H + value;
    IF value < 60 THEN
      clock := clock DIV 40H * 40H + value
    ELSE
      rest := value MOD 60;
      value := value DIV 60 + clock DIV 40H MOD 40H;
      IF value < 60 THEN
        clock := clock DIV 1000H * 1000H + value * 40H + rest
      ELSE
        rest := (value MOD 60) * 40H + rest;
        value := value DIV 60 + clock DIV 1000H MOD 32;
        IF value < 24 THEN
          clock := clock DIV 20000H * 20000H + value * 1000H + rest
        ELSE
          clock := AddDays(clock DIV 20000H, value DIV 24) * 20000H + (value MOD 24) * 1000H + rest;
        END
      END
    END
  END UpdateClock;

  (* begin-procedure-description
---
**Clock** gets the current clock value.
  end-procedure-description *)
  PROCEDURE Clock*(): INTEGER;
  BEGIN UpdateClock; RETURN clock
  END Clock;

  (* begin-procedure-description
---
**SetClock** sets the clock.
  end-procedure-description *)
  PROCEDURE SetClock*(dt: INTEGER);
  BEGIN clock := dt; clockTime := Time()
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
    ELSE (*stop*) LED(w + 192); REPEAT UNTIL FALSE
    END
  END Trap;

  (* begin-procedure-description
---
**Init** is called by Modules on system startup to install a temporary trap handler and then initialize memory and the sector map. 
  end-procedure-description *)
  PROCEDURE Init*;
  BEGIN Install(SYSTEM.ADR(Trap), 20H);  (*install temporary trap*)
    SYSTEM.GET(12, MemLim); SYSTEM.GET(24, heapOrg);
    stackOrg := heapOrg; stackSize := 8000H; heapLim := MemLim;
    list1 := 0; list2 := 0; list3 := 0; list0 := heapOrg;
    clockTime := Time();
    SYSTEM.PUT(list0, heapLim - heapOrg); SYSTEM.PUT(list0+4, -1); SYSTEM.PUT(list0+8, 0);
    allocated := 0; clock := 0; InitSecMap;
    SYSTEM.GET(10000H, clock);
    IF clock = 54696D65H THEN
      SYSTEM.GET(10004H, clockTime);
      SYSTEM.GET(10008H, clock)
    ELSE
      clock := 0
    END;
  END Init;

END Kernel.
