-- Prove2me | Theorems.Thm_Automata_na_concat_inf_run
-- name    : Automata.na_concat_inf_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:25:22.632682+00:00
-- url     : https://prove2.me/theorems/c6df316b-2a1f-4c48-91fb-f8d1694594cf
-- title:
--   Automata: na concat inf run
-- statement:
--   An infinite run of the concatenation NA that contains a state of `M1`
--   consists of a finite run of `M0` followed by an infinite run of `M1`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L195-L278
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Concat.lean#L195-L278

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

theorem Automata.na_concat_inf_run {as : Stream' A} {ss : Stream' (M0.Concat acc0 M1).State} :
    (M0.Concat acc0 M1).InfRun as ss ∧ (∃ n s1, ss n = inr s1) ↔
    ∃ n, (∃ ss0, M0.FinRun n as ss0 ∧ ss0 n ∈ acc0 ∧ ∀ k < n + 1, ss k = inl (ss0 k)) ∧
         (∃ ss1, M1.InfRun (as.drop n) ss1 ∧ ∀ k ≥ n + 1, ss k = inr (ss1 (k - n))) := by sorry
