-- Prove2me | solution 50 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:10.084415+00:00
-- url     : https://prove2.me/submissions/dc64487d-f853-4ee9-bded-50dba065870b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_NymanBeurling_moebius_polynomial_critical_strip_bound
import Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
import Theorems.Thm_NymanBeurling_rational_RH_of_fixed_damping_mean_square
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `NymanBeurling.moebius_polynomial_critical_strip_bound` implies `NymanBeurling.damped_moebius_truncation_mean_square_convergence` (accepted reduction of `NymanBeurling.damped_moebius_truncation_mean_square_convergence`).
section

set_option autoImplicit false
open scoped BigOperators

theorem NymanBeurling.damped_moebius_truncation_mean_square_convergence
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (NymanBeurling.dampedResidualFinite N ε (n+1) -
          NymanBeurling.dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ))) < δ := by
  exact (NymanBeurling.damped_mellin_completion_of_polynomial_bound
    NymanBeurling.moebius_polynomial_critical_strip_bound).1 ε hε hεhalf δ hδ

end

-- Step 2: `NymanBeurling.damped_moebius_truncation_mean_square_convergence` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
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

-- Step 3: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
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
