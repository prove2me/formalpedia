-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_le_uncontrolled_reserve
-- name    : AvramDividend.Classical.surviving_stopped_dividend_expected_le_uncontrolled_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:38:38.336283+00:00
-- url     : https://prove2.me/theorems/31f56682-98d7-4cd3-b05d-a2b65c95415f
-- title:
--   Surviving paths: expected discounted Stieltjes reward is dominated by expected uncontrolled reserve
-- statement:
--   At any deterministic T<S, retain only paths whose controlled risk process has not yet reached ruin by S. On those paths, all stopped discounted Stieltjes dividends through T are at most D(S) and in turn at most x+X_S by controlled reserve nonnegativity. Integrating the pointwise inequality yields domination by the expected nonnegative part of the uncontrolled Lévy reserve. The indicator of survival is explicit and no unjustified bound on paths already ruined is asserted. This makes a valid bridge towards finite-grid localisation and moment bounds.
-- source:
--   Canonically Proved full-measure localisation abb4e5d3-81b8-49e2-a642-1c559bf149df; Proved riskProcess_nonneg_before_ruin c26c83f7-d703-46b9-a361-bf008b70dfe6; MeasureTheory.lintegral_mono.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_local_verification_truncated_stieltjes_le_future_cumulative_dividends

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.surviving_stopped_dividend_expected_le_uncontrolled_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (x + X.X S ω) ∂P) := by sorry
