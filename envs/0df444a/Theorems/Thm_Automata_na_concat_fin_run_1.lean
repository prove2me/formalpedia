-- Prove2me | Theorems.Thm_Automata_na_concat_fin_run_1
-- name    : Automata.na_concat_fin_run_1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:03.657908+00:00
-- url     : https://prove2.me/theorems/974df58c-c578-4755-a702-e1062377b0f1
-- title:
--   Automata: na concat fin run 1
-- statement:
--   A finite run of the concatenation NA that ends in a state of `M1`
--   consists of a run of `M0` followed by a run of `M1`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L98-L190
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L98-L190

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

theorem Automata.na_concat_fin_run_1 {m : ℕ} {as : Stream' A} {ss : Stream' (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).FinRun m as ss ∧ (∃ s1, ss m = inr s1) ↔
    ∃ n < m, (∃ ss0, M0.FinRun n as ss0 ∧ ss0 n ∈ acc0 ∧ ∀ k < n + 1, ss k = inl (ss0 k)) ∧
             (∃ ss1, M1.FinRun (m - n) (as.drop n) ss1 ∧ ∀ k ≥ n + 1, k < m + 1 → ss k = inr (ss1 (k - n))) := by sorry
