-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_random_clock_terminal_expected_le_from_source_regular_direct
-- name    : AvramDividend.Classical.avram_p3_g2_original_BV_random_clock_terminal_expected_le_from_source_regular_direct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T00:34:55.696825+00:00
-- url     : https://prove2.me/theorems/9942cebe-9663-4405-87e7-a64c155b32c5
-- title:
--   Original BV random-clock true terminal L1 and expected post ≤ pre directly from source regularity
-- statement:
--   Direct source-exact theorem at arbitrary bounded measurable random physical clock: both true signed strict-survival postpayment and prepayment HJB terminal values are L1, and their expectations satisfy E[Post]≤E[Pre]. Candidate Borel measurability follows from its actual continuity on nonnegative reserves and zero value on negative reserves, permitting a jump at zero. Both integrability bounds use the actual original Lévy and dividendStrategy, and the terminal comparison is the proved original-source positive-cap right payment inequality at any clock including zero. No extra w-measurable hypothesis, proxy stochastic process, equality-in-law or canonical P3 residual assumption.
-- source:
--   Public Proved 4adbe17d, 10c9f283, 22a17c73, 70ab2405, original source X/D, no Open target imports.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g2_original_BV_random_clock_terminal_expected_le_from_source_regular_direct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    let Post : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0
    Integrable Post P ∧ Integrable Pre P ∧
      (∫ ω, Post ω ∂P) ≤ (∫ ω, Pre ω ∂P) := by sorry
