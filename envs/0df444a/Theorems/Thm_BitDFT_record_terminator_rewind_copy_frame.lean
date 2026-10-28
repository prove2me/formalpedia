-- Prove2me | Theorems.Thm_BitDFT_record_terminator_rewind_copy_frame
-- name    : BitDFT.record_terminator_rewind_copy_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:16:00.926784+00:00
-- url     : https://prove2.me/theorems/04e64321-3fec-4d11-9918-8ae3bb32df03
-- title:
--   Write the record separator, rewind, and copy with a combined runtime bound
-- statement:
--   Let a halted host configuration contain a finite Boolean record on its source tape, with the head immediately after the record, and let its output tape contain a prefix. The separator controller writes the record terminator, after which the rewind and suffix-copy controllers run in sequence. The composed machine reaches its halted output frame, where the original prefix is followed by a copy of the record, within the record length plus the stated fixed controller overhead.
-- source:
--   Composition of the verified record-terminator step, rewind and copy execution, and the finite-controller sequence bound.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots
import Theorems.Thm_BitDFT_machine_sequence_bound
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

theorem BitDFT.record_terminator_rewind_copy_frame (M : MultitapeTM)
    (b : (host M).Cfg) (rest out : List Bool)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (hsource : b.cells (sourceTape M) = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (hsourceHead : b.head (sourceTape M) =
      (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    let P := BitDFT.MachineSequence.sequence
      (BitDFT.MachineSequence.native (host M)) (BitDFT.RecordTerminator.control M)
    let R := BitDFT.RewindTape.control (host M) (sourceTape M)
    let C := control M
    let Q := BitDFT.MachineSequence.sequence R C
    let post : (host M).Cfg := ⟨b.state,
      Function.update b.cells (sourceTape M)
        (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep),b.head⟩
    ∃ t ≤ (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length + rest.length + 7,
      let final := (BitDFT.MachineSequence.sequence P Q).machine.step^[t]
        (BitDFT.MachineSequence.leftCfg P Q
          (BitDFT.MachineSequence.leftCfg
            (BitDFT.MachineSequence.native (host M))
            (BitDFT.RecordTerminator.control M) b))
      final.state = (BitDFT.MachineSequence.sequence P Q).exit ∧
      final.cells = (embed M post.cells
          (Function.update post.head (sourceTape M) 1)
          (fun p => post.cells (host M).inTape p)
          (Function.update post.head (sourceTape M) 1 (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
            rest (out++rest) (rest.length+1))).cells ∧
        final.head = (embed M post.cells
          (Function.update post.head (sourceTape M) 1)
          (fun p => post.cells (host M).inTape p)
          (Function.update post.head (sourceTape M) 1 (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
            rest (out++rest) (rest.length+1))).head := by sorry
