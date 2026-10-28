-- Prove2me | Theorems.Thm_BitDFT_buffer_shift_on_correct
-- name    : BitDFT.buffer_shift_on_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T17:16:07.430615+00:00
-- url     : https://prove2.me/theorems/3716bd80-3b98-43ce-b56b-ec892a842aac
-- title:
--   Caller-compatible buffer shifting preserves all workspace tapes at exact cost
-- statement:
--   For any caller alphabet and tape count, the lifted buffer controller shifts an encoded binary word w in exactly 3|w|+5 transitions. Its output is a blank gap, then w, then the separator, with the head at the gap. The theorem identifies the complete final configuration and explicitly preserves every workspace tape and head at index at least 2.
-- source:
--   Actual controller adapter for the native preprocessor-to-caller composition; no free copies or tape movements are assumed.

import Definitions.Def_BitDFT_BufferShiftOn
open BitDFT.BufferShiftOn BitDFT IntMul

theorem BitDFT.buffer_shift_on_correct (N : MultitapeTM) (base : (machine N).Cfg) (smallBase : BufferShift.machine.Cfg)
    (w : List Bool) :
    let start := embed N base (AlphabetEmbedding.embed (alphabetMap N)
      (BufferShift.frame smallBase .start (w.map BufferShift.machine.bitSym) (w.length+1)))
    let finish := embed N base (AlphabetEmbedding.embed (alphabetMap N)
      (BufferShift.frame smallBase .halt ([.blank]++w.map BufferShift.machine.bitSym++[.sep]) 1))
    (machine N).step^[3*w.length+5] start = finish ∧
      (∀ i : Fin N.k, 2 ≤ i.val → finish.cells i = base.cells i ∧ finish.head i = base.head i) := by sorry
