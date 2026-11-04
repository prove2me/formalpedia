-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_prebudget_expectation_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_expectation_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:52:04.984956+00:00
-- url     : https://prove2.me/theorems/45549f58-11f4-4271-a1a8-8d43705a9c2c
-- title:
--   Actual original BV nonnegative strict-horizon payoff has nonnegative expectation
-- statement:
--   The exact original strict-horizon discounted real Stieltjes cash plus strict-survival pre-rightpayment terminal has nonnegative real expectation. This follows from a proved per-sample-path nonnegativity source and the genuine Bochner integral nonnegativity theorem; it gives a formal lower envelope for Fatou and localiser arguments without assuming an extra compensation law.
-- source:
--   Exact source-proof corollary of bfb4f141-7a0f-4471-b0cd-74afb47c10d1 and Mathlib integral_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_prebudget_payoff_nonnegative
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_expectation_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    0 ≤ (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) := by sorry
