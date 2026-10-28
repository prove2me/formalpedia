-- Prove2me | Theorems.Thm_BitDFT_trim_reverse_correct
-- name    : BitDFT.trim_reverse_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:27:55.731672+00:00
-- url     : https://prove2.me/theorems/db09d511-fc50-46f2-a2e4-47ec49803e21
-- title:
--   Canonical precision bits in exactly 2|w|+4 transitions
-- statement:
--   For any positive-valued little-endian word w, the fixed normalization machine halts after exactly 2|w|+4 transitions. Tape 3 contains exactly the canonical most-significant-bit-first word bin(size(value(w)),value(w)); tape 2 is empty with its head at the marker; the destination head is immediately after its output word. All native input/output and dimension-tape cells and heads are preserved. The entire final configuration is specified, including the cleared source and blank output tail.
-- source:
--   Actual machine normalization of the precision counter output, which may contain high zero padding. The theorem supports exact encNat serialization without assuming the counter already produces canonical digits.

import Definitions.Def_BitDFT_TrimReverse
import Definitions.Def_BitDFT_BinaryCounter
open BitDFT BitDFT.TrimReverse IntMul

theorem BitDFT.trim_reverse_correct (base : machine.Cfg) (w : List Bool) (hw : 0 < BinaryCounter.value w) :
    machine.step^[2*w.length+4] (initial base w) =
      frame base .halt [] (bin (BinaryCounter.value w).size (BinaryCounter.value w)) 0 := by sorry
