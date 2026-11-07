-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
-- name    : AvramDividend.Classical.avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:32:09.719812+00:00
-- url     : https://prove2.me/theorems/7d9dd8ac-36b5-4949-9735-37d028567661
-- title:
--   Original positive-cap controlled dividend Stieltjes gradient density is nonpositive
-- statement:
--   For the actual original dividendStrategy D and riskProcess X x D, the discounted Stieltjes gradient correction 1-deriv w is pointwise nonpositive on the true positive cap-interior payment support B. It uses only canonical HJB gradient sign, exact physical reserve and strictly positive exponential; no stochastic martingale, generator drift or synthetic model. Serves as an independent atom-preserving source component for original signed BV Ito HJB drift.
-- source:
--   Original capped gradient sign; source-exact conditional component of BV-ENV3 turn34 actual original generator plus Stieltjes gradient signed budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn35_original_controlled_dividend_gradient_density_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (B : Ω → Set ℝ)
    (hB : ∀ ω s, s ∈ B ω →
      0 < riskProcess X x D s.toNNReal ω ∧
        ENNReal.ofReal (riskProcess X x D s.toNNReal ω) < C)
    (q : ℝ) :
    ∀ (ω : Ω) (s : ℝ),
      (if s ∈ B ω then
        Real.exp (-(q * s)) *
          (1 - deriv w (riskProcess X x D s.toNNReal ω))
       else 0) ≤ 0 := by sorry
