-- Prove2me | solution 1 for section5_column_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:34.967414+00:00
-- url     : https://prove2.me/submissions/7a61ff5d-fc9e-4362-8bc3-b3a775240e20

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace
theorem solution {n : ℕ}
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (j : Fin n) (hmax : ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1) :
    ‖A v‖ ≤ n*‖A (section5_coordinate_ket j)‖ := by
  have hdecomp : (∑ i : Fin n, v i • section5_coordinate_ket i)=v := by
    ext k
    simp [section5_coordinate_ket,Pi.single_apply]
  have hA : A v=∑ i : Fin n,v i • A (section5_coordinate_ket i) := by
    have hh := congrArg A hdecomp
    simpa only [map_sum,map_smul] using hh.symm
  calc
    ‖A v‖ = ‖∑ i : Fin n,v i • A (section5_coordinate_ket i)‖ := congrArg norm hA
    _ ≤ ∑ i : Fin n,‖v i • A (section5_coordinate_ket i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n,‖A (section5_coordinate_ket j)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have hvi : ‖v i‖ ≤ 1 := (PiLp.norm_apply_le v i).trans_eq hv
      exact (mul_le_mul_of_nonneg_right hvi (norm_nonneg _)).trans (by simpa using hmax i)
    _ = _ := by simp
