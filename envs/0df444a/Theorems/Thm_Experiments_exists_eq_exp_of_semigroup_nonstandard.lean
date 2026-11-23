-- Prove2me | Theorems.Thm_Experiments_exists_eq_exp_of_semigroup_nonstandard
-- name    : Experiments.exists_eq_exp_of_semigroup_nonstandard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:34.647989+00:00
-- url     : https://prove2.me/theorems/2c7583bb-a71f-4e06-8388-04eb009ada68
-- title:
--   Experiments: exists eq exp of semigroup nonstandard
-- statement:
--   **Continuous semigroups are exponentials**, by Euler's infinitesimal argument.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L140-L204
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/NonstandardSemigroup.lean#L140-L204

import Mathlib
import Definitions.Def_Experiments_NonstandardSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A]
variable [NormedAlgebra ℝ A]
variable [CompleteSpace A]

theorem Experiments.exists_eq_exp_of_semigroup_nonstandard [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by sorry
