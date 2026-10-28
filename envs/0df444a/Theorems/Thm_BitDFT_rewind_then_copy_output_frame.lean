-- Prove2me | Theorems.Thm_BitDFT_rewind_then_copy_output_frame
-- name    : BitDFT.rewind_then_copy_output_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:00:48.833975+00:00
-- url     : https://prove2.me/theorems/34d19fea-7a1e-4600-a145-2e1da046e30f
-- title:
--   Rewind a record, then copy it into the final frame
-- statement:
--   If a source tape holds a finite Boolean record followed by a separator and its head is at the separator, the composed controller rewinds the record and hands the unchanged tapes to the suffix copier. It reaches the copier’s halted final frame with the same output prefix and an appended copy of the record. The number of transitions is bounded by the rewind length, one stationary handoff, and the copier run.
-- source:
--   Composition of the exact rewind theorem, workspace identification, the accepted suffix copier, and the accepted finite-controller sequence bound.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_machine_sequence_bound
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.rewind_then_copy_output_frame (M : MultitapeTM)
    (b : (host M).Cfg) (rest out : List Bool)
    (hsource : b.cells (sourceTape M) = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym ++ [TapeCopy.Sym.sep]) p))
    (hsourceHead : b.head (sourceTape M) =
      (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    let P := BitDFT.RewindTape.control (host M) (sourceTape M)
    let Q := control M
    ∃ t ≤ (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length + 2 + 1 +
        (rest.length+1),
      let final := (BitDFT.MachineSequence.sequence P Q).machine.step^[t]
        (BitDFT.MachineSequence.leftCfg P Q ⟨false,b.cells,b.head⟩)
      final.state = Sum.inr Q.exit ∧
        final.cells = (embed M b.cells (Function.update b.head (sourceTape M) 1)
          (fun p => b.cells (host M).inTape p)
          (Function.update b.head (sourceTape M) 1 (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
            rest (out++rest) (rest.length+1))).cells ∧
        final.head = (embed M b.cells (Function.update b.head (sourceTape M) 1)
          (fun p => b.cells (host M).inTape p)
          (Function.update b.head (sourceTape M) 1 (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
            rest (out++rest) (rest.length+1))).head := by sorry
