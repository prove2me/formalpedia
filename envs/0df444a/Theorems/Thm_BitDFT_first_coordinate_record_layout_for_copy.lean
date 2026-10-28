-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_record_layout_for_copy
-- name    : BitDFT.first_coordinate_record_layout_for_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:40:58.308418+00:00
-- url     : https://prove2.me/theorems/8994c8c6-52f8-4243-a1d6-8f4d9320ee4b
-- title:
--   Identify the exact tape record produced by coordinate extraction
-- statement:
--   After signed extraction of a coordinate with sign bit s and magnitude word x, with the requested magnitude prefix present, the record tape contains the start marker followed by s and the first val(y)+1 magnitude bits. Its head is at the first blank cell after that record.
-- source:
--   The exact signed-block final-slot theorem, transported through the first-coordinate machine embedding.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_signed_block_final_slots
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.first_coordinate_record_layout_for_copy (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((sign::x.take (IntMul.val y+1)).map
          BitDFT.SuffixCopyTwoTape.machine.bitSym) p)) ∧
    (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
      (sourceTape M) = ((sign::x.take (IntMul.val y+1)).map
        BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1 := by sorry
