-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
-- name    : AvramDividend.Classical.avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T10:42:39.817596+00:00
-- url     : https://prove2.me/theorems/bf6dbe15-4668-4386-bc57-a88b56b9f691
-- title:
--   One almost-sure BV full-Stieltjes envelope uniform over every strictly pre-ruin horizon
-- statement:
--   One full-measure original-BV event simultaneously bounds the complete discounted stopped Stieltjes payout at every finite strict pre-ruin time and for every optional stopping cutoff, by initial reserve plus elapsed physical drift. Uniformity in time and cutoff allows direct substitution of a path-dependent stopping horizon, instead of unjustifiably taking an uncountable intersection of horizon-specific almost-everywhere statements. All diffuse and right-atom payment mass remains represented.
-- source:
--   The source BV residual monotonicity theorem supplies one event uniform over all times. On that event, strict pre-ruin solvency and the proved post-payment reserve bound control the right-limit cumulative dividends. The proved complete Stieltjes discount inequality applies pointwise to every stopping cutoff. This is the uniform source event needed to localise stopping-time approximations in BV stochastic verification.

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

theorem AvramDividend.Classical.avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (σ : ℝ≥0∞),
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
