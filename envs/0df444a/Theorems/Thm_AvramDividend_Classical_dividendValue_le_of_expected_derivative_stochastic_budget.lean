-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_expected_derivative_stochastic_budget
-- name    : AvramDividend.Classical.dividendValue_le_of_expected_derivative_stochastic_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:51:44.046908+00:00
-- url     : https://prove2.me/theorems/671dd5b8-eece-4478-9de7-464f11480586
-- title:
--   Global dividend verification from the finite-horizon derivative-weighted stochastic budget
-- statement:
--   If an admissible strategy has a verification candidate with gradient at least one along dividend payment times, integrable derivative-weighted discounted payments, and a uniform expected derivative-weighted finite-horizon bound by the initial candidate value, then the complete infinite-horizon dividend value is at most that initial candidate value. This isolates the nontrivial stopped stochastic-calculus estimate needed to prove the verification bound.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_iSup_expected_derivative_weighted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_expected_derivative_stochastic_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D)
    (hStrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u : Ω → ℝ → ℝ)
    (hgrad : ∀ ω t, t ∈ paymentTimes (ruinTime X x D ω) →
      1 ≤ deriv w (u ω t))
    (hWeighted : ∀ n : ℕ, ∀ ω : Ω,
      IntegrableOn (fun t : ℝ =>
        Real.exp (-(q * t)) * deriv w (u ω t))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ))
        (dividendMeasure D ω))
    (hBudget : ∀ n : ℕ,
      (∫⁻ ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) * deriv w (u ω t)
            ∂(dividendMeasure D ω)) ∂P) ≤ ENNReal.ofReal (w x)) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by sorry
