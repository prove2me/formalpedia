-- Prove2me | Theorems.Thm_BitDFT_record_suffix_copy_workspace_match_after_separator
-- name    : BitDFT.record_suffix_copy_workspace_match_after_separator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:29:27.511955+00:00
-- url     : https://prove2.me/theorems/0efeb408-41b0-4ed5-ae08-50d212aef6cb
-- title:
--   Identify the copier workspace after separator insertion
-- statement:
--   If the source tape contains a finite encoded record, its head is at the first blank cell after that record, and the output tape contains the encoded prefix with its head at the next blank cell, then inserting a separator at the source head yields exactly the routed initial workspace required by the suffix copier. All other work tapes remain unchanged.
-- source:
--   Composition of the accepted separator insertion theorem with the exact finite-time suffix-copy adapter.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
import Theorems.Thm_BitDFT_record_terminator_sequence_step
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.record_suffix_copy_workspace_match_after_separator (M : MultitapeTM)
    (b : (host M).Cfg) (pre rest out : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        ((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (hsourceHead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1)
    (houtput : b.cells (host M).outTape =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p)))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    Function.update b.cells (sourceTape M)
      (Function.update (b.cells (sourceTape M)) (b.head (sourceTape M)) (host M).sep) =
        (embed M b.cells b.head (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
            (pre++rest) out (pre.length+1))).cells := by sorry
