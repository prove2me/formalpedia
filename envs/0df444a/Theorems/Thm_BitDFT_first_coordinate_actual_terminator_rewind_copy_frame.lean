-- Prove2me | Theorems.Thm_BitDFT_first_coordinate_actual_terminator_rewind_copy_frame
-- name    : BitDFT.first_coordinate_actual_terminator_rewind_copy_frame
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T21:20:06.065615+00:00
-- url     : https://prove2.me/theorems/039b0c06-55fb-410c-baa3-86fc6a056af5
-- title:
--   Append a completed coordinate record using the actual machine stages
-- statement:
--   After the signed-coordinate extractor has produced its signed bit record, the record is terminated, rewound, and copied into the output tape. The resulting frame contains the previous output followed by that coordinate record. The bound includes the separator-writing controller, both controller handoffs, rewinding, and copying.
-- source:
--   Composition of the accepted signed-block record layout with the actual separator, rewind, and suffix-copy machine stages.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_SuffixCopyTwoTape
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_signed_block_final_slots
import Theorems.Thm_BitDFT_machine_sequence_bound
open BitDFT.RecordSuffixCopy BitDFT.SuffixCopyTwoTape IntMul

theorem BitDFT.first_coordinate_actual_terminator_rewind_copy_frame (M : MultitapeTM)
    (c : (BitDFT.VectorReady.machine M).Cfg)
    (rootCells : ℕ → TapeCopy.Sym) (rootHead : ℕ)
    (sign : Bool) (x y : List Bool) (hx : IntMul.val y+1 ≤ x.length)
    (out : List Bool)
    (houtput : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).cells
      (host M).outTape = fun p =>
        encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
          (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : (BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y).head
      (host M).outTape = out.length+1) :
    let record := sign::x.take (IntMul.val y+1)
    let b := BitDFT.FirstCoordinate.final M c rootCells rootHead sign x y
    let P := BitDFT.MachineSequence.sequence
      (BitDFT.MachineSequence.native (host M)) (BitDFT.RecordTerminator.control M)
    let R := BitDFT.RewindTape.control (host M) (sourceTape M)
    let C := control M
    let Q := BitDFT.MachineSequence.sequence R C
    let post : (host M).Cfg := ⟨b.state,
      Function.update b.cells (sourceTape M)
        (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep),b.head⟩
    ∃ t ≤ (record.map BitDFT.SuffixCopyTwoTape.machine.bitSym).length + record.length + 7,
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
            record (out++record) (record.length+1))).cells ∧
        final.head = (embed M post.cells
          (Function.update post.head (sourceTape M) 1)
          (fun p => post.cells (host M).inTape p)
          (Function.update post.head (sourceTape M) 1 (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
            record (out++record) (record.length+1))).head := by sorry
