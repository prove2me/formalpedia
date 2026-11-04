-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:31:34.072985+00:00
-- url     : https://prove2.me/theorems/c49b143d-880a-4454-9215-0d0691388847
-- title:
--   Original source right-dividend absolute signed Itô correction bounded by the discounted physical cash envelope
-- statement:
--   For the original X jump followed by dividend right payment, assume the exact hjump secant inequality, genuine pre-ruin eligibility, nonnegative dividend right increments, summable physical discounted cash and local Lipschitz secant control by K≥1. The signed rightjump remainder is nonpositive termwise, its absolute series converges and the total absolute correction is bounded by the explicit (K−1)-times-discounted-physical-cash series. This is a stopped pathwise envelope suitable for obtaining L1 integrability of the Itô residual from actual cash L1, provided a uniform/localised K and actual indexed payment series are established. It adds no boundary derivative assumption or finite-jump-activity premise.
-- source:
--   Avram Prop 4(i) post-source jump correction; accepted P4-D local secant signed summability e4e52ea2, rightjump sign 9f4070e7; Mathlib Summable.tsum_le_tsum and tsum absolute summability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_countable_rightjump_local_secant_summable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_rightjump_absolute_remainder_cash_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D s ω - D s ω ≤
        w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    {ι : Type*} (t : ι → ℝ≥0) (ω : Ω)
    (hPre : ∀ i : ι, t i = 0 ∨ (t i : ℝ≥0∞) < ruinTime X x D ω)
    (K : ℝ) (hK : 1 ≤ K)
    (hPayNonneg : ∀ i : ι, 0 ≤ rightLimit D (t i) ω - D (t i) ω)
    (hPaySummable : Summable (fun i : ι =>
      Real.exp (-(q * (t i : ℝ))) *
        (rightLimit D (t i) ω - D (t i) ω)))
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
        (Real.exp (-(q * (t i : ℝ))) *
          (rightLimit D (t i) ω - D (t i) ω))) := by sorry
