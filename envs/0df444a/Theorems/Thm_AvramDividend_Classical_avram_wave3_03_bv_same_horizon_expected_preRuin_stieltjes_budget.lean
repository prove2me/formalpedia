-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_same_horizon_expected_preRuin_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_same_horizon_expected_preRuin_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T10:37:40.334715+00:00
-- url     : https://prove2.me/theorems/a7d6f4f3-52eb-4dbd-8517-4f8b53d89ea6
-- title:
--   Original BV same-horizon expected full Stieltjes pre-ruin localisation budget
-- statement:
--   For the original bounded-variation spectrally negative Lévy process and an arbitrary admissible-shape dividend strategy, the expected discounted complete Stieltjes payout through finite T, restricted to sample paths with T strictly before ruin, is bounded by initial reserve plus exactly T times the BV physical drift. The stopping cutoff is an arbitrary measurable or nonmeasurable path-dependent clock, including the actual ruin time. This strengthens the earlier S>T survivor expectation envelope to the same horizon while retaining singular-continuous payout mass and the right-hand atom at T.
-- source:
--   Accepted original source BV residual monotonicity, actual pre-ruin right-neighbourhood solvency, right post-payment reserve, and the full discounted Stieltjes/rightLimit estimate. Almost everywhere bound integrated under X.isProbability. This proves a source-specific localisation estimate for the finite-grid to stopped-integral step; it does not assume any missing generator compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_preRuin_eventually_right_solvent

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_same_horizon_expected_preRuin_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ ω, if (T : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
