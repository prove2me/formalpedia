-- Prove2me | Theorems.Thm_Experiments_NSA_exists_eq_exp_of_semigroup
-- name    : Experiments.NSA.exists_eq_exp_of_semigroup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:26:16.583937+00:00
-- url     : https://prove2.me/theorems/d4368ed8-b933-4e40-ab7c-142d0825da5e
-- title:
--   NSA: exists eq exp of semigroup
-- statement:
--   **Continuous semigroups are exponentials**, in nonstandard language.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/UltrapowerSemigroup.lean#L28-L167
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/UltrapowerSemigroup.lean#L28-L167

import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_Experiments_Ultrapower
import Definitions.Def_Experiments_UltrapowerSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments Experiments.NSA
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem Experiments.NSA.exists_eq_exp_of_semigroup [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by sorry
