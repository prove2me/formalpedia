-- Prove2me | solution 33 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:29:44.863833+00:00
-- url     : https://prove2.me/submissions/534699c4-43c4-48ea-9841-eef4827d6490
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_rational_RH_of_fixed_damping_mean_square
import Theorems.Thm_NymanBeurling_damped_moebius_truncation_mean_square_convergence
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `NymanBeurling.damped_moebius_truncation_mean_square_convergence` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (_hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  by_cases hhigh : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hhigh
  · intro hz
    have hline := NymanBeurling.rational_RH_of_fixed_damping_mean_square
      (fun ε hε hεhalf ↦ NymanBeurling.damped_moebius_truncation_mean_square_convergence
        ε hε hεhalf 1 zero_lt_one)
      s (by linarith) (lt_of_not_ge hhigh) hz
    linarith

end

-- Step 2: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
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
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
