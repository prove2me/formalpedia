-- Prove2me | Theorems.Thm_BitDFT_record_terminator_step
-- name    : BitDFT.record_terminator_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:34:09.949789+00:00
-- url     : https://prove2.me/theorems/08707311-cb11-4d92-a7be-46b5a7e1743b
-- title:
--   One-step separator insertion on the scratch tape
-- statement:
--   Let the record-terminator controller start in its entry state, with arbitrary tape contents and head positions. If the cell under the scratch head is blank, one transition writes the separator there, leaves every other cell unchanged, and leaves every head in place.
-- source:
--   A verified low-level step used to delimit the signed coordinate record before its low-bit block is copied.

import Definitions.Def_BitDFT_RecordTerminator
open BitDFT.RecordTerminator IntMul

theorem BitDFT.record_terminator_step (M : MultitapeTM) (cells : Fin (storage M).k → ℕ → (storage M).Sym)
    (head : Fin (storage M).k → ℕ)
    (hblank : cells (target M) (head (target M)) = (storage M).blank) :
    (controlMachine M).step ⟨false,cells,head⟩ =
      ⟨true, Function.update cells (target M)
        (Function.update (cells (target M)) (head (target M)) (storage M).sep), head⟩ := by sorry
