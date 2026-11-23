-- Prove2me | Theorems.Thm_Automata_na_loop_fin_run
-- name    : Automata.na_loop_fin_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:06.746367+00:00
-- url     : https://prove2.me/theorems/6e20cb57-4b50-432a-b579-70e44eab7e72
-- title:
--   Automata: na loop fin run
-- statement:
--   A finite run of the loop NA that contains the `inl ()` marker only
--   at the beginning and at the end is an accepting run of `M`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L63-L135
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L63-L135

import Definitions.Def_AutomataTheory_Automata_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Automata_Loop
set_option autoImplicit true
open Function Set Sum Filter Stream'
open Classical
open scoped Computability
attribute [local instance_reducible] Stream'
open Automata
variable {A : Type}
attribute [local instance_reducible] NA.Loop
variable {M : NA A} {acc : Set M.State}

theorem Automata.na_loop_fin_run {n : ℕ} {as : Stream' A} {ss : Stream' (M.Loop acc).State} (h : n > 0) :
    (M.Loop acc).FinRun n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k ∈ range inr) ↔
    ∃ ss', M.FinRun n as ss' ∧ ss' n ∈ acc ∧ ss 0 = inl () ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by sorry
