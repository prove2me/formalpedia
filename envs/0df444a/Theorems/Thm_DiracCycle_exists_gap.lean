-- Prove2me | Theorems.Thm_DiracCycle_exists_gap
-- name    : DiracCycle.exists_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:48:36.252899+00:00
-- url     : https://prove2.me/theorems/a633176d-1a70-4d27-9a40-a474c6145593
-- title:
--   Dirac Cycle: exists gap
-- statement:
--   Pigeonhole: if `R` has at least `#U + 2` elements, two elements of `R` have no element of `U`
--   strictly between them.
--
--   Source: https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L185-L221
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean#L185-L221

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
public import Definitions.Def_DiracCycleLib_DiracCycle
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open DiracCycle
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}

theorem DiracCycle.exists_gap : ∀ (n : ℕ) (R U : Finset ℕ), #U = n → #U + 2 ≤ #R →
    ∃ a ∈ R, ∃ b ∈ R, a < b ∧ ∀ u ∈ U, ¬ (a < u ∧ u < b) := by sorry
