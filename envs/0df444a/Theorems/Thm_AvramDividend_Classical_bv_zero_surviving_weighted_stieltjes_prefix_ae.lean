-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_weighted_stieltjes_prefix_ae
-- name    : AvramDividend.Classical.bv_zero_surviving_weighted_stieltjes_prefix_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:11:13.142979+00:00
-- url     : https://prove2.me/theorems/6345392b-4da4-4778-b624-197eab8ced9a
-- title:
--   Finite-activity zero-barrier surviving prefixes pay the exact drift Stieltjes dividend stream
-- statement:
--   For each deterministic horizon T, on almost every sample path that strictly survives the original zero-barrier reflected drawdown stopping clock beyond T, every nonnegative-weighted Stieltjes dividend integral on (0,T] equals the same integral against drift-scaled Lebesgue measure. Use the accepted finite-activity mesh proof that strictly surviving positive residuals are null, the accepted BV almost-sure nonnegative residual, and the accepted conditional Stieltjes equality for zero-residual prefixes. This gives the exact dividend stream before the first negative jump and is reusable for the stopped payout identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 following Proposition 1 and equation (3.14), using Prove2Me accepted process-level Stieltjes lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_zero_deficit_weighted_stieltjes_prefix_ae
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_zero_surviving_weighted_stieltjes_prefix_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by sorry
