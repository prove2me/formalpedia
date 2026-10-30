-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_surviving_stieltjes_drift_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_surviving_stieltjes_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:18:31.943394+00:00
-- url     : https://prove2.me/theorems/c6800b11-b161-4311-a765-4e456cddc13c
-- title:
--   Full BV surviving stopped Stieltjes dividends bounded by initial capital plus physical drift
-- statement:
--   For a bounded-variation spectrally negative Lévy source and a genuine left-continuous dividend strategy, almost surely every surviving horizon S dominates the entire discounted Stieltjes payout through an earlier time T by the deterministic reserve envelope x+S times physical drift. The payment measure retains continuous mass, right jumps and time-zero dividends. This gives a local pathwise deterministic payout bound useful for BV stopping and uniform-integrability localisation.
-- source:
--   Combine the Proved almost-sure monotonicity of the actual Lévy drift deficit d*t-X_t with the Proved complete stopped dividend Stieltjes payout bound by x+X_S strictly before ruin. No jump-only decomposition, conditional budget hypothesis or replacement measure is assumed.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_surviving_stieltjes_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (S : ℝ) * X.drift) := by sorry
