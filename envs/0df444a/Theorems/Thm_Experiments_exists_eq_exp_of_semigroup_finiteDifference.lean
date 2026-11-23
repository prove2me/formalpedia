-- Prove2me | Theorems.Thm_Experiments_exists_eq_exp_of_semigroup_finiteDifference
-- name    : Experiments.exists_eq_exp_of_semigroup_finiteDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:53:15.119798+00:00
-- url     : https://prove2.me/theorems/38cc938e-9638-4651-b85d-b6872cec44b3
-- title:
--   Experiments: exists eq exp of semigroup finite Difference
-- statement:
--   **Continuous semigroups are exponentials**, by finite differences and compactness.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L112-L130
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/Experiments/FiniteDifferenceSemigroup.lean#L112-L130

import Definitions.Def_Experiments_GeneratorBound
import Definitions.Def_Experiments_FiniteDifferenceSemigroup
set_option autoImplicit true
open Filter NormedSpace Set
open scoped Topology
noncomputable section
open Experiments
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem Experiments.exists_eq_exp_of_semigroup_finiteDifference [FiniteDimensional ℝ A] (M : ℝ → A)
    (hcont : ContinuousOn M (Ici 0)) (h0 : M 0 = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → M (s + t) = M s * M t) :
    ∃ a : A, ∀ t, 0 ≤ t → M t = exp (t • a) := by sorry
