-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
-- name    : AvramDividend.Classical.stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:37:11.165076+00:00
-- url     : https://prove2.me/theorems/dd79a58f-5e44-4015-82a4-83b5bf5f697a
-- title:
--   Before ruin, stopped discounted Stieltjes dividends are controlled by the uncontrolled Lévy reserve
-- statement:
--   For a dividend strategy D, if S is strictly before controlled ruin and T<S, the complete discounted Stieltjes payout through T and any stopping cut-off σ is at most ENNReal.ofReal(x+X_S). First bound the whole continuous-plus-jump reward by D(S) using the newly proved Stieltjes localisation lemma. Then use nonnegativity of the controlled reserve U_S=x+X_S−D(S) strictly before ruin. This gives a practical local payout bound in terms of the uncontrolled Lévy process, useful for localised expectation estimates.
-- source:
--   Canonically Proved local_verification_truncated_stieltjes_le_future_cumulative_dividends (abb4e5d3-81b8-49e2-a642-1c559bf149df) and riskProcess_nonneg_before_ruin (c26c83f7-d703-46b9-a361-bf008b70dfe6).

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_le_future_cumulative_dividends

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S)
    (hSurv : (S : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (x + X.X S ω) := by sorry
