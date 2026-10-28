-- Prove2me | Theorems.Thm_BitDFT_copy_from_rewound_record
-- name    : BitDFT.copy_from_rewound_record
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:48:02.012279+00:00
-- url     : https://prove2.me/theorems/b4ac1229-8b07-4750-bfeb-1befa15ed097
-- title:
--   Copy the terminated record from its rewound configuration
-- statement:
--   From the routed suffix-copier configuration identified by a terminated source record at cell one and a specified output prefix, the copier appends the entire record to the output in exactly one handoff plus one transition per record symbol and its final separator check. The resulting configuration is the exact embedded halted copier state.
-- source:
--   Composition of the exact suffix-copy simulation with the rewound-record workspace identification.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.copy_from_rewound_record (M : MultitapeTM)
    (b : (host M).Cfg) (rest out : List Bool)
    (hsource : b.cells (sourceTape M) = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (rest.map BitDFT.SuffixCopyTwoTape.machine.bitSym ++ [TapeCopy.Sym.sep]) p))
    (hsourceHead : b.head (sourceTape M) = 1)
    (houtput : b.cells (host M).outTape = fun p =>
      encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (out.map BitDFT.SuffixCopyTwoTape.machine.bitSym) p))
    (houtputHead : b.head (host M).outTape = out.length+1) :
    (routed M).step^[rest.length+1]
      ⟨(embed M b.cells b.head (fun p => b.cells (host M).inTape p)
          (b.head (host M).inTape)
          (BitDFT.SuffixCopyTwoTape.frame
            (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .copy rest out 1)).state,
        b.cells,b.head⟩ =
      embed M b.cells b.head (fun p => b.cells (host M).inTape p)
        (b.head (host M).inTape)
        (BitDFT.SuffixCopyTwoTape.frame
          (BitDFT.SuffixCopyTwoTape.machine.initCfg [] []) .halt rest (out++rest)
          (rest.length+1)) := by sorry
