-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_bounded_random_horizon_expected_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_bounded_random_horizon_expected_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T10:46:09.495038+00:00
-- url     : https://prove2.me/theorems/6cb573d2-aab1-4c91-839c-46c9dd063f16
-- title:
--   Uniform expected BV full-Stieltjes localisation at bounded sample-dependent horizons
-- statement:
--   For every path-dependent time T(ω) bounded by deterministic H, and every path-dependent payment cutoff σ(ω), the expected discounted full Stieltjes payment up to T(ω) on paths where that time precedes the true source ruin is at most initial capital plus H times the positive part of the physical bounded-variation drift. This deterministic finite bound is uniform over all such bounded random horizons and is therefore suited to finite-grid stopping-time localisation and dominated convergence. The formula preserves diffuse dividend mass and right-at-horizon payments.
-- source:
--   Use the already Proved source BV drift-deficit monotonicity event, original pre-ruin eventual-right solvency, post-payment reserve right-limit, and full Stieltjes payment estimate directly at Tω and σω. The same full-measure event works at all random horizons. Since 0≤Tω≤H, (Tω)*drift≤H*max 0 drift. The constant upper bound then integrates exactly using the original source IsProbabilityMeasure P. No false jump-atomic concentration assumption is used; no generator compensation is concluded.

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

theorem AvramDividend.Classical.avram_wave3_03_bv_bounded_random_horizon_expected_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T : Ω → ℝ≥0) (H : ℝ≥0) (hTH : ∀ ω, T ω ≤ H) :
    (∫⁻ ω, if ((T ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic ((T ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) := by sorry
