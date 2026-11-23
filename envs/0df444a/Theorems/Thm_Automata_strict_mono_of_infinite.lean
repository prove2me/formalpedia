-- Prove2me | Theorems.Thm_Automata_strict_mono_of_infinite
-- name    : Automata.strict_mono_of_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:25.171558+00:00
-- url     : https://prove2.me/theorems/6b36a51e-109e-49ee-8ee8-055e3bc97bb9
-- title:
--   Automata: strict mono of infinite
-- statement:
--   The Automata construction uses the strict mono of infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L153-L157
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/BuchiCongr.lean#L153-L157

import Definitions.Def_AutomataTheory_Automata_Pair
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
set_option autoImplicit true
open Function Set Filter Stream'
open Automata
attribute [local instance_reducible] NA.BuchiCongr
open Classical
variable {A : Type}
variable {M : NA A} {acc : Set M.State}

theorem Automata.strict_mono_of_infinite {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by sorry
