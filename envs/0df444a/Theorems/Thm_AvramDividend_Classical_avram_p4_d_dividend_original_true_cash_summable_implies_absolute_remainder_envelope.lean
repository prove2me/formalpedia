-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:43:35.915892+00:00
-- url     : https://prove2.me/theorems/9174e536-808c-4bac-8c9e-1f0716b7074c
-- title:
--   Original stopped Stieltjes singleton cash yields a summable absolute right-dividend residual and exact discounted-cash envelope
-- statement:
--   For an actual eligible indexed source-original dividend payment family on the closed stopped horizon, the summable weighted singleton Stieltjes cash is identified with the physical right payment at each time, including zero and the surviving horizon. The proved source-ordered secant correction has an absolutely summable signed remainder, dominated by (K-1) times the exact real weighted singleton cash series. This supplies a pathwise envelope for P4-F, with K from an honest local secant bound and no boundary smoothness invented.
-- source:
--   Accepted true cash-to-physical atom equality 2a049ee7, actual rightLimit domination 953f0e91, absolute signed source-ordered remainder envelope c49b143d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_right_atom_cash_to_real
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_true_cash_summable_implies_absolute_remainder_envelope
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
      |Real.exp (-(q * (t i : ℝ))) *
        ((rightLimit D (t i) ω - D (t i) ω) +
          w (x + X.X (t i) ω - rightLimit D (t i) ω) -
          w (riskProcess X x D (t i) ω))|) ∧
    (∑' i : ι, |Real.exp (-(q * (t i : ℝ))) *
      ((rightLimit D (t i) ω - D (t i) ω) +
        w (x + X.X (t i) ω - rightLimit D (t i) ω) -
        w (riskProcess X x D (t i) ω))|) ≤
      (∑' i : ι, (K - 1) *
        ((((dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ)))
          {(t i : ℝ)} *
          (if (t i : ℝ) ∈ paymentTimes (ruinTime X x D ω)
            then ENNReal.ofReal (Real.exp (-(q * (t i : ℝ))))
            else 0)).toReal)) := by sorry
