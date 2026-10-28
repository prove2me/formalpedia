-- Prove2me | Theorems.Thm_BitDFT_rewind_record_tape_to_start
-- name    : BitDFT.rewind_record_tape_to_start
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:36:27.240396+00:00
-- url     : https://prove2.me/theorems/4b5303fc-394b-4471-882f-ff12cba5becb
-- title:
--   Rewind a terminated record tape to its first symbol
-- statement:
--   Let a source tape contain the encoded finite word formed by a record followed by a separator, with its head at the separator. The start marker occurs only at cell zero. The rewind controller returns the head to cell one in exactly the word length plus two transitions, preserving the entire tape configuration.
-- source:
--   Composition of the encoded record layout with the accepted exact-clock rewind controller.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_rewind_tape_correct
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.rewind_record_tape_to_start (M : MultitapeTM)
    (b : (host M).Cfg) (pre rest : List Bool)
    (hsource : b.cells (sourceTape M) =
      (fun p => encode M (BitDFT.SuffixCopyTwoTape.machine.tapeOf
        (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym) ++ [TapeCopy.Sym.sep]) p)))
    (hhead : b.head (sourceTape M) = ((pre++rest).map
      BitDFT.SuffixCopyTwoTape.machine.bitSym).length+1) :
    (BitDFT.RewindTape.machine (host M) (sourceTape M)).step^[
      (((pre++rest).map BitDFT.SuffixCopyTwoTape.machine.bitSym).length+2)]
      ⟨false,b.cells,b.head⟩ =
      BitDFT.RewindTape.frame (host M) (sourceTape M) b true 1 := by sorry
