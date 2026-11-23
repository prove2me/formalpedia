-- Prove2me | Theorems.Thm_Automata_na_loop_fin_run_exists
-- name    : Automata.na_loop_fin_run_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:06.826192+00:00
-- url     : https://prove2.me/theorems/b5fe95a3-9fa8-4da2-8212-a524b921c7a8
-- title:
--   Automata: na loop fin run exists
-- statement:
--   Conversely, for any finite accepting run of `M`, there is a finite run of the
--   loop NA that contains the `inl ()` marker only at the beginning and at the end.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L140-L150
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Loop.lean#L140-L150

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

theorem Automata.na_loop_fin_run_exists {n : ℕ} {as : Stream' A} {ss' : Stream' M.State}
    (h_run' : M.FinRun n as ss') (h_acc' : ss' n ∈ acc) :
    ∃ ss, (M.Loop acc).FinRun n as ss ∧ ss n = inl () ∧ (∀ k < n, k > 0 → ss k = inr (ss' k)) := by sorry
