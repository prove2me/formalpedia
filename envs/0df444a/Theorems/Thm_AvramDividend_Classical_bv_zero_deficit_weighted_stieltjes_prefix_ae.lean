-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_deficit_weighted_stieltjes_prefix_ae
-- name    : AvramDividend.Classical.bv_zero_deficit_weighted_stieltjes_prefix_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:21:14.67381+00:00
-- url     : https://prove2.me/theorems/f932bd49-28da-4399-88d9-538d992f8d08
-- title:
--   Actual BV zero-deficit paths have drift-weighted Stieltjes reward on every finite prefix
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process satisfying Standing, the drift residual remains zero up to a fixed horizon whenever it is zero at the horizon, almost surely. Consequently the genuine reflected running-supremum dividend Stieltjes measure on the whole half-open initial interval equals drift-scaled Lebesgue measure, for every nonnegative weight. This is the source-faithful pathwise input for proving the first-jump reward identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), immediately after Proposition 1, finite-activity zero-barrier argument, equation (3.14); Prove2Me proved actual BV compensated monotonicity and Stieltjes interval uniqueness.

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_drift_deficit_zero_time_forces_linear_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_deficit_weighted_stieltjes_prefix_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      X.drift * (T : ℝ) - X.X T ω = 0 →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
