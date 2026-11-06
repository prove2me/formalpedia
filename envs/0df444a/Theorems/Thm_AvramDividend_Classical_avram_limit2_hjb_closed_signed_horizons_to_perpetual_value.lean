-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:00:15.459588+00:00
-- url     : https://prove2.me/theorems/595875b3-02bb-47a5-a1c2-9298fe0deb79
-- title:
--   Original capped BV HJB signed closed-horizon budget gives perpetual dividend value and integrable terminals
-- statement:
--   If the original bounded-variation spectrally negative Levy control satisfies the exact signed stopped closed-horizon dividend-cash plus postpayment-terminal expectation estimate at every positive horizon, the genuine HJB gradient condition yields terminal integrability at each horizon and the perpetual dividendValue bound, preserving Iic horizon cash and ruin boundary atoms.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_original_signed_horizons_and_terminal_to_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_hjb_closed_signed_horizons_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) ≤ w x) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω => (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0)) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
