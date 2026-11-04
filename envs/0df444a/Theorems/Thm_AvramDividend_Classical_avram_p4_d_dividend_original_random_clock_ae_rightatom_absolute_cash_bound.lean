-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:09:58.806017+00:00
-- url     : https://prove2.me/theorems/1be1b311-f201-488f-9b27-b593dcce2f41
-- title:
--   Exact random stopped-clock original right-dividend signed series and absolute bound by Cash
-- statement:
--   For the canonical original Lévy dividend process and path-dependent finite stopping horizon, consider an injective path-dependent enumeration of all selected actual payment times inside the horizon. Under the explicit canonical right-dividend hjump hypothesis and a source-local uniform K secant upper bound, the signed discounted atomic remainder is absolutely summable and nonpositive; its absolute sum is at most (K-1) times the exact original stopped Cash. The statement preserves the original post-X-jump pre-dividend state and all time-zero and eligible terminal payments. It is a pathwise bound lifted almost surely; it does not invent measurability of random enumerations nor global L1 integrability without a proper measurable selection.
-- source:
--   Public Proved fd02394f-5507-4e61-84bd-1c01ea9e0895, exact canonical P4-F Cash; honest local K supplied as hypothesis, not inferred from interior C2 regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_rightatom_absolute_cash_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤ w (riskProcess X x D s ω) -
        w (riskProcess X x D s ω - (rightLimit D s ω - D s ω)))
    (t : Ω → ι → ℝ≥0) (τ : Ω → ℝ≥0)
    (hT : ∀ ω i, t ω i ≤ τ ω)
    (hPay : ∀ ω i, (t ω i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hInj : ∀ ω, Function.Injective (fun i : ι => (t ω i : ℝ)))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ ω i,
      w (riskProcess X x D (t ω i) ω) -
        w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) ≤
          K * (rightLimit D (t ω i) ω - D (t ω i) ω))
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ᵐ ω ∂P,
      let J : ι → ℝ := fun i => Real.exp (-(q * (t ω i : ℝ))) *
        ((rightLimit D (t ω i) ω - D (t ω i) ω) +
          w (x + X.X (t ω i) ω - rightLimit D (t ω i) ω) -
          w (riskProcess X x D (t ω i) ω))
      Summable J ∧ (∑' i : ι, J i) ≤ 0 ∧
        Summable (fun i : ι => |J i|) ∧
        (∑' i : ι, |J i|) ≤ (K - 1) * Cash ω := by sorry
