-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_strict_horizon_prebudget_implies_perpetual_dividendValue
-- name    : AvramDividend.Classical.avram_limit1_bv_strict_horizon_prebudget_implies_perpetual_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:04:37.747168+00:00
-- url     : https://prove2.me/theorems/578eb26d-5652-461c-a62e-c3e226f87d72
-- title:
--   Original BV positive strict stopped HJB budgets imply full genuine discounted dividend value
-- statement:
--   Exact original-process bounded-variation cap-dividend value passage assuming only the source-specific positive-real-horizon stopped HJB budget. Public proved LIMIT-1 preflight derives admissible jump secant and derivative lower bound from the stated HJB; public proved BV original strict budget to closed Iic T Stieltjes cash bridge retains terminal atoms; the pinned dividendValue supremum lemma and closed-horizon set monotonicity yield genuine full perpetual dividendValue. No martingale source is invented. The unresolved hypothesis is precisely the original P3 positive-horizon prebudget a19d8b28 for every T.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_bv_strict_horizon_prebudget_implies_perpetual_dividendValue
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
    (hBudget : ∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
         else 0) ∂P) ≤ w x) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
