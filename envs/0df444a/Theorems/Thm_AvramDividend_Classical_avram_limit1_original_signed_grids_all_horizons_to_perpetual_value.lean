-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_signed_grids_all_horizons_to_perpetual_value
-- name    : AvramDividend.Classical.avram_limit1_original_signed_grids_all_horizons_to_perpetual_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:26:34.666669+00:00
-- url     : https://prove2.me/theorems/f23aad42-a530-4dc3-bac1-e86afddd57f3
-- title:
--   Uniform original BV signed grids imply untruncated discounted dividend value
-- statement:
--   Once the genuine original BV P3 signed nonnegative compensated Fatou grid witness is available at every positive finite real horizon, Proved LIMIT-1 inclusive-horizon cash and Proved full dividendValue as increasing natural closed-horizon supremum give the true perpetual value bound. Uses n+1 to cover n=0 and retains zero-time, right-horizon and ruin atoms; does not assume terminal vanishing or original martingale compensation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_limit1_original_signed_grids_all_horizons_to_perpetual_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hGrid : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      ∃ F M B : ℕ → Ω → ℝ,
        (∀ n, Measurable (F n)) ∧
        (∀ n, Integrable (F n) P) ∧
        (∀ n, 0 ≤ᵐ[P] F n) ∧
        (∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
          (∫ ω, M n ω + B n ω ∂P) ≤ 0) ∧
        (∀ n, ∀ᵐ ω ∂P, F n ω ≤ w x + (M n ω + B n ω)) ∧
        (∀ᵐ ω ∂P,
          let S : ℝ≥0 := ⟨T, hT⟩
          ENNReal.ofReal (
            (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)).toReal +
            (if (S : ℝ≥0∞) < ruinTime X x D ω then
              Real.exp (-(q * T)) * w (riskProcess X x D S ω)
            else 0)) ≤
          liminf (fun n => ENNReal.ofReal (F n ω)) atTop)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
