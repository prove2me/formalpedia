-- Prove2me | solution 1 for p2m_path_sum_complementarity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:36:24.041993+00:00
-- url     : https://prove2.me/submissions/a0cdea74-eb99-4a52-a4c7-8e9554f505ed

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_VanderbeiLP_PathFollowing_PathFollowingMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Matrix VanderbeiLP.PathFollowing
section
theorem solution {k : ℕ} (x z dx dz : Fin k → ℝ) (μ : ℝ)
    (hcomp : ∀ i, z i * dx i + x i * dz i = μ - x i * z i) :
    (∑ i : Fin k, (z i * dx i + x i * dz i)) =
      (k : ℝ) * μ - z ⬝ᵥ x := by
  classical
  rw [dotProduct]
  calc
    _ = ∑ i : Fin k, (μ - x i * z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hcomp i
    _ = _ := by simp [Finset.sum_sub_distrib, Finset.sum_const, mul_comm]
end
