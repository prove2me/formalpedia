-- Prove2me | solution 25 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:33:30.005725+00:00
-- url     : https://prove2.me/submissions/331acb1c-6ae7-4ebc-80d3-ac75ca0f7983
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_rh_zeta_zero_free_right_half
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis := by
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have e : (1 - s).re = 1 - s.re := by simp
    exact rh_zeta_zero_free_right_half (1 - s) (by rw [e]; linarith) (by rw [e]; linarith) hfe
  · exact heq
  · exact absurd hz (rh_zeta_zero_free_right_half s hgt h1)
