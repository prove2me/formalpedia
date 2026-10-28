-- Prove2me | Theorems.Thm_BitDFT_record_suffix_copy_correct
-- name    : BitDFT.record_suffix_copy_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T20:10:20.823987+00:00
-- url     : https://prove2.me/theorems/a4aaec68-7b04-4312-8fe1-97677dfbef23
-- title:
--   Copy a record suffix inside a preserved caller workspace
-- statement:
--   For any caller workspace and any two-tape copier configuration whose input contains a delimited bit string, the routed caller machine copies the specified suffix to the output in exactly one transition per bit plus one separator-detection transition. It preserves the input and every parked caller tape and head, and halts in the embedded copier's exact final configuration.
-- source:
--   The exact-runtime adapter needed to feed the extracted low-precision operand to the integer multiplication routine.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Theorems.Thm_BitDFT_two_tape_suffix_copy_correct
open BitDFT.RecordSuffixCopy IntMul

theorem BitDFT.record_suffix_copy_correct (M : MultitapeTM)
    (cells : Fin (host M).k → ℕ → (host M).Sym)
    (heads : Fin (host M).k → ℕ)
    (rootCells : ℕ → (encoded M).Sym) (rootHead : ℕ)
    (base : BitDFT.SuffixCopyTwoTape.machine.Cfg)
    (pre rest out : List Bool) :
    (routed M).step^[rest.length+1]
      (embed M cells heads rootCells rootHead
        (BitDFT.SuffixCopyTwoTape.frame base .copy (pre++rest) out (pre.length+1))) =
      embed M cells heads rootCells rootHead
        (BitDFT.SuffixCopyTwoTape.frame base .halt (pre++rest) (out++rest)
          (pre.length+rest.length+1)) := by sorry
