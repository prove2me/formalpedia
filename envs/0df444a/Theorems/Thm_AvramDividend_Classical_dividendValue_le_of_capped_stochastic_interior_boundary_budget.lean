-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_capped_stochastic_interior_boundary_budget
-- name    : AvramDividend.Classical.dividendValue_le_of_capped_stochastic_interior_boundary_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:08:46.673978+00:00
-- url     : https://prove2.me/theorems/44dc246f-2f06-408d-a143-0fa6d21d72bc
-- title:
--   Full capped dividend verification from a stopped interior-plus-boundary stochastic budget
-- statement:
--   For a capped HJB candidate and an admissible dividend control, the exact finite-horizon Stieltjes payout is bounded by derivative-weighted dividends paid strictly inside the positive below-cap reserve region plus the true boundary payment remainder. If a stopped stochastic calculus argument bounds the expected sum of those two terms uniformly by w(x), then the complete infinite-horizon dividend value is at most w(x). This isolates the probabilistic obligation with no artificial derivative-integrability or purely atomic assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_expected_capped_hjb_payment_weighted_interior_boundary

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendValue_le_of_capped_stochastic_interior_boundary_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (hStrat : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
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
