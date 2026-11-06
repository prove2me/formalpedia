-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_bv_hjb_signed_terminal_to_perpetual
-- name    : AvramDividend.Classical.avram_limit2_bv_hjb_signed_terminal_to_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T07:48:19.741418+00:00
-- url     : https://prove2.me/theorems/6bd2e50e-fd42-464e-a63b-2bad16eb9e40
-- title:
--   Original BV HJB and signed closed stopped cash imply integrable terminal and perpetual dividend bound
-- statement:
--   For the original bounded-variation spectrally negative Levy process, the canonical HJB max equality implies the interior derivative bound 1 ≤ deriv w y. Given exact original positive closed-horizon signed stopped dividend cash plus the post-right-payment survival terminal expectation bounded by w x, the Proved LIMIT-1 direct BV terminal-and-value theorem yields integrability of the genuine terminal at every positive horizon and the perpetual dividendValue upper bound. Time-zero payments and closed right-horizon atoms remain in the original paymentTimes(ruinTime) ∩ Iic T. The stochastic signed stopped budget is an explicit hypothesis; no terminal vanishing, martingale identity or equality-in-law is inferred.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit1_bv_direct_postpayment_terminal_to_dividendValue

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_bv_hjb_signed_terminal_to_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
      let Term : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) +
        (∫ ω, Term ω ∂P) ≤ w x) :
    (∀ (T : ℝ) (hT : 0 ≤ T), 0 < T →
      let S : ℝ≥0 := ⟨T, hT⟩
      Integrable (fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0) P) ∧
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
