-- Prove2me | Theorems.Thm_BitDFT_rewound_record_workspace_match
-- name    : BitDFT.rewound_record_workspace_match
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:48:03.903209+00:00
-- url     : https://prove2.me/theorems/7c614556-0cbd-42f6-9414-ac259895f21f
-- title:
--   Identify the copier frame after a record rewind
-- statement:
--   If a terminated record is on the source tape with its head rewound to cell one, and the output tape has the specified encoded prefix and head, then the complete workspace and head vector equal the initial routed suffix-copier frame. The caller's input tape and every parked work tape are preserved in the embedding.
-- source:
--   The tape and head interface lemmas for the routed suffix copier.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.rewound_record_workspace_match (M : MultitapeTM)
    (b : (host M).Cfg) (rest out : List Bool)
    (hsource : b.cells (sourceTape M) = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym ++ [TapeCopy.Sym.sep]) p))
    (hsourceHead : b.head (sourceTape M) = 1)
    (houtput : b.cells (host M).outTape = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    b.cells = (embed M b.cells b.head
      (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
      (BitDFT.SuffixCopyTwoTape.frame (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
        rest out 1)).cells ∧
    b.head = (embed M b.cells b.head
      (fun p => b.cells (host M).inTape p) (b.head (host M).inTape)
      (BitDFT.SuffixCopyTwoTape.frame (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy
        rest out 1)).head := by sorry
