-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_budget_le_literal_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_all_eligible_rightjump_signed_budget_le_literal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:55:11.974641+00:00
-- url     : https://prove2.me/theorems/73f72dc7-74f0-4240-a388-0412b961e12c
-- title:
--   All eligible original post-source dividend right-jump corrections are signed and absolutely summable below canonical stopped cash
-- statement:
--   For any injectively indexed genuine original pre-ruin or initial payment times, including arbitrary zero right jumps, the source-ordered discounted dividend Itô correction is summable, nonpositive, and absolutely summable. Its real total variation is bounded by (K-1) times the precise original full Stieltjes ruin-truncated Cash integral, preserving initial and surviving terminal right atoms, simultaneous source/payment jumps, and singular-continuous mass. Uses the already established source-bound all-eligible budget and exact restricted-to-literal cash identity; K is an explicit honest secant envelope.
-- source:
--   Accepted original P4-D positive-atom and closed-stopped-cash identity; independently published all-eligible atomic signed budget; Avram Proposition 4(i), Eq. (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Every eligible original right-payment correction, including zero right jumps, is signed and dominated by the literal stopped cash. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_all_eligible_rightjump_signed_budget_le_literal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i, t i ≤ T)
    (hPre : ∀ i, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : Function.Injective (fun i : ι => (t i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i, w (riskProcess X x D (t i) ω) -
      w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
        K * (rightLimit D (t i) ω - D (t i) ω)) :
    let J : ι → ℝ := fun i => Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))
    Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
      Summable (fun i : ι => |J i|) ∧
      (∑' i : ι, |J i|) ≤
        (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by sorry
