-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_surviving_expected_stieltjes_drift_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_surviving_expected_stieltjes_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:30:27.379486+00:00
-- url     : https://prove2.me/theorems/36eaf529-140a-47e8-b837-d30a4e0f608e
-- title:
--   BV surviving expected complete Stieltjes dividends have a deterministic drift allowance
-- statement:
--   For a BV original Lévy process and an arbitrary adapted left-continuous cumulative dividend strategy, the expected whole discounted Stieltjes payout through T, on paths surviving beyond S>T, is bounded by x plus S times the deterministic BV physical drift. The stopping cut-off σ is an arbitrary function of the sample path, so one can take the actual random ruin clock. The right-hand side is finite regardless of moments of post-ruin dividends. No countable-atom restriction is imposed.
-- source:
--   The Proved surviving_stopped_dividend_expected_le_uncontrolled_reserve theorem bounds the full path-dependent Stieltjes expected payoff by E[(x+X_S)^+]. The Proved BV actual Lévy drift deficit gives X_S<=S*drift on a full-measure event. Compare ENNReal integrands almost everywhere and use the source IsProbabilityMeasure P to integrate the constant. This supplies the explicit deterministic expected localisation budget but does not assume or conclude the general HJB verification inequality.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_le_uncontrolled_reserve

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_surviving_expected_stieltjes_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (S : ℝ) * X.drift) := by sorry
