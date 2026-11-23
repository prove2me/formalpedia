-- Prove2me | Theorems.Thm_Automata_na_sum_fin_run
-- name    : Automata.na_sum_fin_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:29:13.641485+00:00
-- url     : https://prove2.me/theorems/847b611c-3d9f-4f38-ba64-539f3588303f
-- title:
--   Automata: na sum fin run
-- statement:
--   The Automata construction uses the na sum fin run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L35-L74
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Sum.lean#L35-L74

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Sum
set_option autoImplicit true
open Function Set Filter Stream'
attribute [local implicit_reducible] Stream'
open Automata
variable {I A : Type}
attribute [local instance_reducible] NA.Sum
variable {M : I → NA A}

theorem Automata.na_sum_fin_run {n : ℕ} {as : Stream' A} {ss : Stream' (NA.Sum M).State} :
    (NA.Sum M).FinRun n as ss ↔ ∃ i ss_i, (M i).FinRun n as ss_i ∧ ∀ k < n + 1, ss k = ⟨i, ss_i k⟩ := by sorry
