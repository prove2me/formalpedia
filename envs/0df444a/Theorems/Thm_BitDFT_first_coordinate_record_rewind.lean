-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_record_rewind
-- name    : BitDFT.first_coordinate_record_rewind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:40:53.121193+00:00
-- url     : https://prove2.me/theorems/b906889b-1f1b-4876-b304-07629474de96
-- title:
--   Terminate and rewind the extracted coordinate record
-- statement:
--   If signed extraction leaves the first-coordinate record on its scratch tape, then writing a separator after the record and running the rewind controller returns the scratch head to cell one. The rewind takes exactly the record length plus two transitions and preserves the tape contents.
-- source:
--   Composition of the signed-block final-slot theorem, separator insertion, and the exact rewind theorem.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.first_coordinate_record_rewind (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool)
    (hx : IntMul.val y+1 ≤ x.length) :
    let record := (sign::x.take (IntMul.val y+1))
    let b := BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y
    let post : (host M).Cfg :=
      ⟨b.state,
        Function.update b.cells (sourceTape M)
          (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep),
        b.head⟩
    (BitDFT.RewindTape.machine (host M) (sourceTape M)).step^[
      ((record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+2)]
      ⟨false,post.cells,post.head⟩ =
      BitDFT.RewindTape.frame (host M) (sourceTape M) post true 1 := by sorry
