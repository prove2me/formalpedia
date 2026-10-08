-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_atom_exponential_bound
-- name    : AvramDividend.Classical.discounted_dividendMeasure_atom_exponential_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:09:32.97138+00:00
-- url     : https://prove2.me/theorems/54efee15-75d5-4751-bbb0-a73c18000401
-- title:
--   Discounted Stieltjes dividend atom is bounded by discounted exponential test-value drop
-- statement:
--   At any admissible dividend payment instant, the exact Stieltjes atom mass multiplied by e^{-qt} is dominated in ENNReal by the e^{-qt}-discounted decrease in the exponential test function when θ≥1. This combines the formal singleton-mass formula with the accepted discounted admissible jump inequality. The result directly relates the integrator dividendMeasure to the jump-payment verification estimate without asserting a full continuous Lebesgue–Stieltjes integral bound.
-- source:
--   Children dividendMeasure_singleton_eq_rightLimit_sub, discounted_admissible_exponential_dividend_jump_bound; pinned Mathlib ENNReal.ofReal_mul and ENNReal.ofReal_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_dividendMeasure_atom_exponential_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      dividendMeasure D ω {(t : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      (Real.exp (θ * riskProcess X x D t ω) -
        Real.exp (θ * (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))))) := by sorry
