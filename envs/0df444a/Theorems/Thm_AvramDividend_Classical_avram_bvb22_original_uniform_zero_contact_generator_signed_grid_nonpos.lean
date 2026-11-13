-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_uniform_zero_contact_generator_signed_grid_nonpos
-- name    : AvramDividend.Classical.avram_bvb22_original_uniform_zero_contact_generator_signed_grid_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:58:12.835191+00:00
-- url     : https://prove2.me/theorems/0c78ad8f-b2e3-43df-8439-fff2b6d6b7d7
-- title:
--   Original finite-activity uniform grid zero-contact signed generator contribution is nonpositive
-- statement:
--   The original physical finite uniform grid can include left-limit reserve exactly equal to zero. Each such cell contributes the exact physical BV drift, discounted value and entire negative-mark kernel. Under the original Standing, BV, finite-activity, HJB, admissibility-compatible hypotheses, the original source origin generator contribution is nonpositive; nonnegative discounted cell widths preserve the sign. Finite summation gives a signed zero-contact budget without excluding open-mask boundary cases.
-- source:
--   Accepted exact original origin generator inequality 0344aae3, positive exponential, original physical monotone grid; Avram-Palmowski-Pistorius (2007), (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_reserve_full_finite_activity_generator_HJB
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb22_original_uniform_zero_contact_generator_signed_grid_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1))
    (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n + 1),
      if Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) = 0 then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.drift - q * w 0 +
            (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0 := by sorry
