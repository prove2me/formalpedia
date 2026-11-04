-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:54:49.217331+00:00
-- url     : https://prove2.me/theorems/fd02394f-5507-4e61-84bd-1c01ea9e0895
-- title:
--   True paymentTimes alone guarantee source-eligible signed and cash-dominated right-dividend correction at every indexed time
-- statement:
--   For any injective enumeration of nonnegative original paymentTimes before a closed horizon, the original paymentTimes membership already guarantees time zero or strict pre-ruin. Therefore no extra pointwise survival or strict positivity assumption is needed for the exact source post-Lévy/pre-dividend right-jump signed and absolute sum bound by original canonical ruin-stopped Stieltjes Cash. Uses the proved paymentTimes strict-survival-or-zero decomposition and the full eligible P4-D budget with an explicit honest local K secant bound. Positive ruin atoms remain correctly excluded.
-- source:
--   Accepted original paymentTimes strict-survival-or-zero, full cash identity, independent all-eligible P4-D signed budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_eligible_rightjump_signed_absolute_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original paymentTimes membership already guarantees each real payment index is initial or strictly pre-ruin. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
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
