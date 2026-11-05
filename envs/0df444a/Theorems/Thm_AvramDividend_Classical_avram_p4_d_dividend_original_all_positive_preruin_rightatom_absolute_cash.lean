-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T19:51:29.124757+00:00
-- url     : https://prove2.me/theorems/1ced3e97-18a0-44da-8d45-06d06b78b3fa
-- title:
--   Entire actual positive pre-ruin stopped rightpayment series is summable and Cash-dominated
-- statement:
--   For all strictly positive original right-dividend payments strictly before ruin and at or before the closed horizon, the canonical post-X pre-D secant correction is absolutely summable, nonpositive, and bounded in absolute value by (K-1) times the exact discounted original Stieltjes Cash. The pointwise K secant condition is explicit and does not assume global boundary regularity. The true paymentTimes membership is derived from the strict survival condition, while simultaneous source/payment jumps and the horizon atom are retained.
-- source:
--   Accepted original original_paymentTimes_all_rightjump_budget_no_preruin_premise fd02394f and paymentTimes_eq_strict_of_pos 7c01995b, instantiated on the exact set of all positive pre-ruin right-dividend atoms through the closed horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_all_positive_preruin_rightatom_absolute_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧ t ≤ T ∧
      0 < rightLimit D t ω - D t ω})
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ t : B,
      w (riskProcess X x D (t : ℝ≥0) ω) -
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) ≤
          K * (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) :
    let J : B → ℝ := fun t => Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
      ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
        w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
        w (riskProcess X x D (t : ℝ≥0) ω))
    Summable J ∧ (∑' t : B, J t) ≤ 0 ∧
      Summable (fun t : B => |J t|) ∧
      (∑' t : B, |J t|) ≤ (K - 1) *
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
