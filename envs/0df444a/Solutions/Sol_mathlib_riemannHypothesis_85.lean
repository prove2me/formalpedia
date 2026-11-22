-- Prove2me | solution 85 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:45:51.502802+00:00
-- url     : https://prove2.me/submissions/d9d8e96f-d820-4c85-b906-332b21ea0091
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_zeta_ne_zero_of_strip_of_two_lt_abs_im
import Theorems.Thm_XiQuantitativePublished_zeta_zero_free_height_three
import Theorems.Thm_XiPairingPublished_concrete_xi_no_real_zeros
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

theorem solution : RiemannHypothesis := by
  -- Step 1: zeta has no zeros with 1/2 < Re s < 1.
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
    intro s h0 h1 hz
    have hre0 : 0 < s.re := by linarith
    rcases lt_or_ge 2 |s.im| with him | him
    · exact zeta_ne_zero_of_strip_of_two_lt_abs_im s h0 h1 him hz
    · have habs := abs_le.mp him
      rcases lt_trichotomy s.im 0 with hneg | hzero | hpos
      · -- lower half-plane: reflect by complex conjugation
        have hc : riemannZeta ((starRingEnd ℂ) s) = 0 := by
          rw [riemannZeta_conj, hz, map_zero]
        have e1 : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
        have e2 : ((starRingEnd ℂ) s).im = -s.im := Complex.conj_im s
        exact XiQuantitativePublished.zeta_zero_free_height_three ((starRingEnd ℂ) s)
          (by rw [e1]; exact hre0) (by rw [e1]; exact h1) (by rw [e2]; linarith)
          (by rw [e2]; linarith) hc
      · -- real axis: the xi function has no real zeros
        have hs : s = ((s.re : ℝ) : ℂ) := by
          apply Complex.ext
          · simp
          · simp [hzero]
        have hs0 : s ≠ 0 := by
          intro h
          rw [h] at hre0
          simp at hre0
        have hs1 : s ≠ 1 := by
          intro h
          rw [h] at h1
          simp at h1
        have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
        have hΛ : completedRiemannZeta s = 0 := by
          have h := riemannZeta_def_of_ne_zero hs0
          rw [hz] at h
          rcases div_eq_zero_iff.mp h.symm with h' | h'
          · exact h'
          · exact absurd h' (Complex.Gammaℝ_ne_zero_of_re_pos hre0)
        have hΛ0 : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
          have h := completedRiemannZeta_eq s
          rw [hΛ] at h
          linear_combination -h
        have hxi : (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2 = 0 := by
          rw [hΛ0]
          field_simp
          ring
        have hno := XiPairingPublished.concrete_xi_no_real_zeros s.re
        rw [← hs] at hno
        exact hno hxi
      · exact XiQuantitativePublished.zeta_zero_free_height_three s hre0 h1 hpos (by linarith) hz
  -- Step 2: reflect the left half of the strip by the functional equation.
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
    exact hright (1 - s) (by rw [e]; linarith) (by rw [e]; linarith) hfe
  · exact heq
  · exact absurd hz (hright s hgt h1)
