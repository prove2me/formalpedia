-- Prove2me | Theorems.Thm_Automata_na_concat_fin_run_0
-- name    : Automata.na_concat_fin_run_0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:25:09.632406+00:00
-- url     : https://prove2.me/theorems/5fe467c4-5b0a-4c73-87dd-3242596f2d6f
-- title:
--   Automata: na concat fin run 0
-- statement:
--   A finite run of the concatenation NA that ends in a state of `M0`
--   is completely a run of `M0`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L57-L93
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L57-L93

import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Automata_Concat
set_option autoImplicit true
open Function Set Filter Sum Stream'
open Classical
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.Concat
variable {M0 M1 : NA A} {acc0 : Set M0.State}

theorem Automata.na_concat_fin_run_0 {m : ℕ} {as : Stream' A} {ss : Stream' (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s0, ss m = inl s0) ↔
    (∃ ss0, M0.FinRun m as ss0 ∧ ∀ k < m + 1, ss k = inl (ss0 k)) := by sorry
