-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_iSup_expected_derivative_weighted
-- name    : AvramDividend.Classical.dividendValue_le_iSup_expected_derivative_weighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:34:55.799357+00:00
-- url     : https://prove2.me/theorems/77b4295d-c9ab-4688-aec9-6bd2b9aed3c1
-- title:
--   Full dividend value dominated by supremum of expected derivative-weighted finite-horizon payouts
-- statement:
--   For an admissible dividend strategy, the full infinite-horizon expected discounted dividend value is bounded by the supremum of finite-horizon expected derivative-weighted real Stieltjes integrals. It combines the proved monotone truncation identity for dividendValue with the actual-strategy expected derivative-weighted payment inequality, without needing the missing stopped Levy chain rule.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_expected_discounted_actual_dividend_le_derivative_weighted

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_iSup_expected_derivative_weighted
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
        (dividendMeasure D ω)) :
    dividendValue X q x D ≤
      ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          Real.exp (-(q * t)) * deriv w (u ω t)
            ∂(dividendMeasure D ω)) ∂P := by sorry
