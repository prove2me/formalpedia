-- Prove2me | Theorems.Thm_BitDFT_record_suffix_copy_after_record_separator_from_tapes
-- name    : BitDFT.record_suffix_copy_after_record_separator_from_tapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:31:04.548078+00:00
-- url     : https://prove2.me/theorems/62a25b39-f125-435a-b42a-b6ff23c60b93
-- title:
--   Copy a record suffix after separator insertion
-- statement:
--   Suppose a halted extraction has written a finite encoded record and prefix on its source and output tapes, respectively, with both heads at the required boundaries. If its remaining tape heads match the copier's initial layout, then separator insertion followed by the suffix copier takes exactly |r|+4 transitions and reaches the halted configuration with the suffix appended to the output.
-- source:
--   Composition of the accepted separator insertion theorem with the exact finite-time suffix-copy adapter and its tape-workspace interface.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.record_suffix_copy_after_record_separator_from_tapes (M : MultitapeTM)
    (b : (host M).Cfg)
    (hstate : b.state = (host M).qHalt)
    (hblank : b.cells (sourceTape M) (b.head (sourceTape M)) = (host M).blank)
    (pre rest out : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (hsourceHead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (houtputHead : b.head (host M).outTape = out.length+1)
    (hheads : b.head = (embed M b.cells b.head
      (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
      (BitDFT.SuffixCopyTwoTape.frame
        (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
        (pre++rest) out (pre.length+1))).head) :
    let P := BitDFT.MachineSequence.sequence (BitDFT.MachineSequence.native (host M))
      (BitDFT.RecordTerminator.control M)
    let Q := control M
    (BitDFT.MachineSequence.sequence P Q).machine.step^[rest.length+4]
      (BitDFT.MachineSequence.leftCfg P Q
        (BitDFT.MachineSequence.leftCfg (BitDFT.MachineSequence.native (host M))
          (BitDFT.RecordTerminator.control M) b)) =
      BitDFT.MachineSequence.rightCfg P Q
        ⟨(embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).state,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).cells,
          (embed M b.cells b.head (fun p => b.cells (host M).inTape p)
            (b.head (host M).inTape)
            (BitDFT.SuffixCopyTwoTape.frame
              (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt
              (pre++rest) (out++rest) (pre.length+rest.length+1))).head⟩ := by sorry
