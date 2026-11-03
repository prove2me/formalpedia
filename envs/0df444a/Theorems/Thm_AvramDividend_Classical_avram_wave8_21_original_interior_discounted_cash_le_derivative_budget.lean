-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_interior_discounted_cash_le_derivative_budget
-- name    : AvramDividend.Classical.avram_wave8_21_original_interior_discounted_cash_le_derivative_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:38:27.090362+00:00
-- url     : https://prove2.me/theorems/c0c8d269-176a-4488-bd31-962a72555d34
-- title:
--   Original interior Stieltjes discounted continuous-payment cash below derivative budget
-- statement:
--   For the exact original dividendMeasure D ω on a measurable time region A at which the controlled reserve lies strictly between zero and the cap, if the discounted cash and discounted candidate derivative integrands are integrable, the full original signed discounted cash integral is no larger than the corresponding derivative-weighted integral. This is the explicit continuous-mass inequality used with the separate rightpayment atom bounds; it assumes no false interiority at the reserve boundaries.
-- source:
--   Avram original Stieltjes-controlled dividend verification, reusing proved W7-02 interior gradient sign.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_interior_discounted_cash_le_derivative_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (A : Set ℝ) (hA : MeasurableSet A)
    (hregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hCash : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      A (dividendMeasure D ω))
    (hDeriv : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω))
      A (dividendMeasure D ω)) :
    (∫ t in A, Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
      (∫ t in A, Real.exp (-(q * t)) *
        deriv w (riskProcess X x D t.toNNReal ω)
        ∂(dividendMeasure D ω)) := by sorry
