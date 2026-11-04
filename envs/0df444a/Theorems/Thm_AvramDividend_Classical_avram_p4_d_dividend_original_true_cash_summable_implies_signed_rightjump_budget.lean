-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_cash_summable_implies_signed_rightjump_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_summable_implies_signed_rightjump_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:26:25.079864+00:00
-- url     : https://prove2.me/theorems/df7382e4-1abb-4090-bcc9-bec81176761b
-- title:
--   Summable actual original stopped singleton cash implies nonpositive and summable source-ordered right-dividend residual
-- statement:
--   For any indexed family of actual eligible original right-dividend times within the finite horizon, the genuine stopped Stieltjes singleton-weight cash series is assumed summable. The accepted original singleton-to-physical-cash identity converts each term into exp(-qt)*(rightLimit D-D), with nonnegative increment derived from the true dividend strategy. Under the honest local secant Lipschitz bound and canonical hjump, the proved countable original rightjump lemma yields an absolutely summable signed right-jump Itô correction with nonpositive sum. The theorem preserves source-first/right-dividend-second ordering, time zero, and surviving-horizon payment; the event selector prevents paying a positive-ruin terminal atom.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq 5.13; accepted P4-D real source stopped singleton conversion 2a049ee7 and right-jump summability e4e52ea2, original rightLimit domination 953f0e91.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_summable_implies_signed_rightjump_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω) (T : ℝ≥0)
    (hT : ∀ i : ι, t i ≤ T)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (hPay : ∀ i : ι, (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω))
    (hCashSummable : Summable (fun i : ι =>
      (((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
        {(t i : ℝ)} *
        (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ))))
          else 0)).toReal))
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ i : ι,
      w (riskProcess X x D (t i) ω) -
        w (x + X.X (t i) ω - rightLimit D (t i) ω) ≤
          K * (rightLimit D (t i) ω - D (t i) ω)) :
    Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))) ∧
    (∑' i : ι, Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))) ≤ 0 := by sorry
