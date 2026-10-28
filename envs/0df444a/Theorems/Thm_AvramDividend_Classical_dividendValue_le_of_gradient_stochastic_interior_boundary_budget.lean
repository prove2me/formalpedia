-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_gradient_stochastic_interior_boundary_budget
-- name    : AvramDividend.Classical.dividendValue_le_of_gradient_stochastic_interior_boundary_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:51:04.581+00:00
-- url     : https://prove2.me/theorems/0b843cc4-aea6-452a-a516-4ee69fb216dd
-- title:
--   Full-horizon dividend verification from interior gradient and expected stochastic budget
-- statement:
--   For any admissible dividend strategy and any candidate value with derivative at least one on strictly positive interior reserve states, a uniform expected interior-weighted-plus-boundary stochastic budget at each truncated horizon bounds the entire infinite-horizon discounted dividend value. This variant only uses the derivative inequality needed for bounded variation; generator drift estimates remain a separate stochastic-calculus obligation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_expected_capped_gradient_payment_weighted_interior_boundary

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_gradient_stochastic_interior_boundary_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (hStrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (u : Ω → ℝ → ℝ)
    (hInterior : ∀ ω, MeasurableSet
      {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C})
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω,
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) ∩
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
            ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ)) \
          {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)) ∂P) ≤ ENNReal.ofReal (w x)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
