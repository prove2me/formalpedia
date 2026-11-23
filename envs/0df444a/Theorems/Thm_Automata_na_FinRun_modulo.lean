-- Prove2me | Theorems.Thm_Automata_na_FinRun_modulo
-- name    : Automata.na_FinRun_modulo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:16:45.186294+00:00
-- url     : https://prove2.me/theorems/ab524e48-f570-4a5c-8f7e-55a31207fe2a
-- title:
--   Automata: na Fin Run modulo
-- statement:
--   The Automata construction uses the na Fin Run modulo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L189-L194
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Basic.lean#L189-L194

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
variable {A : Type} {M : NA A}

theorem Automata.na_FinRun_modulo {n : ℕ} {as as' : Stream' A} {ss ss' : Stream' M.State}
    (ha : ∀ k < n, as k = as' k) (hs : ∀ k < n + 1, ss k = ss' k) (hr : M.FinRun n as ss) : M.FinRun n as' ss' := by sorry
