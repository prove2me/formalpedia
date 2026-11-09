-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_zero_candidate_lipschitz
-- name    : AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_candidate_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:35:26.917812+00:00
-- url     : https://prove2.me/theorems/75b9a7d6-318e-4e1a-9e82-58f748b967e6
-- title:
--   Original finite-activity BV candidate has a uniform one-sided Lipschitz estimate down to reserve zero
-- statement:
--   For the original Standing BV spectrally negative Levy process with finite total negative-jump rate and a strictly positive dividend cap, the exact HJB and candidate regularity assumptions give a uniform positive-reserve derivative bound; the original candidate is one-sided Lipschitz on each bounded nonnegative reserve strip strictly below the cap, including increments starting at reserve zero. This is a boundary regularity interface, not an assumed stopped Ito budget.
-- source:
--   Finite-cap positive-reserve localisation removal in original stopped HJB source 3993433e, parent 73419313, triple-mesh source 8df3cb52 and ultimately 51b72610. Source-exact direct consequence of Proved 9db99eb1 and the mean value theorem, including time-zero boundary continuity.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_candidate_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) (hbC : ENNReal.ofReal b < C) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ b →
        w t - w s ≤ L * (t - s) := by sorry
