-- Prove2me | solution 1 for e7_continuous_test_zero_of_polynomial_approx
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T08:51:01.343681+00:00
-- url     : https://prove2.me/submissions/460128d0-3c34-4bd2-8ce3-c2e94bbc03da

import Mathlib

open MeasureTheory Set Filter

/-- If a continuous test function is uniformly approximable by polynomials on `[0,1]`,
and every polynomial-weighted integral of `G` vanishes, then the `φ`-weighted integral
vanishes as well (using that `G` is supported on `[0,1]`). -/
theorem solution (G φ : ℝ → ℝ)
    (hGint : IntegrableOn G (Set.Ioi (0 : ℝ)) volume)
    (hGzero : ∀ y : ℝ, 1 < y → G y = 0)
    (hpoly : ∀ p : Polynomial ℝ,
      IntegrableOn (fun y : ℝ => p.eval y * G y)
          (Set.Ioi (0 : ℝ)) volume ∧
        (∫ y, p.eval y * G y
          ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0)
    (hφint : IntegrableOn (fun y : ℝ => φ y * G y)
      (Set.Ioi (0 : ℝ)) volume)
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ p : Polynomial ℝ, ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
        ‖φ y - p.eval y‖ ≤ ε) :
    (∫ y, φ y * G y ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = 0 := by
  set μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ
  set A : ℝ := ∫ y, ‖G y‖ ∂μ with hA
  have hA0 : 0 ≤ A := integral_nonneg (fun y => norm_nonneg _)
  have hmain : ∀ ε > 0, ‖∫ y, φ y * G y ∂μ‖ ≤ ε * A := by
    intro ε hε
    obtain ⟨p, hp⟩ := happrox ε hε
    have hsub' : Integrable (fun y => φ y * G y - p.eval y * G y) μ :=
      hφint.sub (hpoly p).1
    have hsub : Integrable (fun y => (φ y - p.eval y) * G y) μ := by
      refine hsub'.congr ?_
      filter_upwards with y
      ring
    have hsplit : (∫ y, φ y * G y ∂μ) - ∫ y, p.eval y * G y ∂μ =
        ∫ y, (φ y - p.eval y) * G y ∂μ := by
      rw [← integral_sub hφint (hpoly p).1]
      apply integral_congr_ae
      filter_upwards with y
      ring
    have hIeq : ∫ y, φ y * G y ∂μ = ∫ y, (φ y - p.eval y) * G y ∂μ := by
      rw [← hsplit, (hpoly p).2, sub_zero]
    rw [hIeq]
    have hpoint : ∀ᵐ y ∂μ, ‖(φ y - p.eval y) * G y‖ ≤ ε * ‖G y‖ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy0 : 0 ≤ y := le_of_lt hy
      rcases le_or_gt y 1 with hy1 | hy1
      · have hmem : y ∈ Set.Icc (0:ℝ) 1 := ⟨hy0, hy1⟩
        have hφp : ‖φ y - p.eval y‖ ≤ ε := hp y hmem
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hφp (norm_nonneg _)
      · simp [hGzero y hy1]
    calc ‖∫ y, (φ y - p.eval y) * G y ∂μ‖
        ≤ ∫ y, ‖(φ y - p.eval y) * G y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, ε * ‖G y‖ ∂μ :=
          integral_mono_ae hsub.norm (hGint.norm.const_mul ε) hpoint
      _ = ε * A := by rw [integral_const_mul, hA]
  have hI0 : ‖∫ y, φ y * G y ∂μ‖ = 0 := by
    by_contra hne
    have hne' : (∫ y, φ y * G y ∂μ) ≠ 0 := by
      intro h
      exact hne (by simp [h])
    have hpos : 0 < ‖∫ y, φ y * G y ∂μ‖ := norm_pos_iff.mpr hne'
    have hε : 0 < ‖∫ y, φ y * G y ∂μ‖ / (2 * (A + 1)) := by positivity
    have hb := hmain _ hε
    have hfrac : A / (A + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have heq : (‖∫ y, φ y * G y ∂μ‖ / (2 * (A + 1))) * A =
        (A / (A + 1)) * (‖∫ y, φ y * G y ∂μ‖ / 2) := by
      field_simp
    have hb2 : (‖∫ y, φ y * G y ∂μ‖ / (2 * (A + 1))) * A ≤
        ‖∫ y, φ y * G y ∂μ‖ / 2 := by
      rw [heq]
      exact mul_le_of_le_one_left (by positivity) hfrac
    linarith
  exact norm_eq_zero.mp hI0
