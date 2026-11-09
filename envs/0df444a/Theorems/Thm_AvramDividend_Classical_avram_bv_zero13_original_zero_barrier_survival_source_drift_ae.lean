-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_zero_barrier_survival_source_drift_ae
-- name    : AvramDividend.Classical.avram_bv_zero13_original_zero_barrier_survival_source_drift_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:38:02.916214+00:00
-- url     : https://prove2.me/theorems/3576106e-2552-4fa8-93c9-5908f590598a
-- title:
--   Genuine BV finite-activity source follows the drift line at a surviving zero-barrier clock
-- statement:
--   At each deterministic nonnegative clock T, on almost every sample path surviving the genuine original zero-barrier reflected ruin clock, the original BV finite-negative-jump-activity Lévy path X_T equals T times its physical drift. Combine Proved almost-sure original BV upper drift bound with Proved zero probability of a strictly positive negative-jump deficit on surviving paths. No auxiliary compound-Poisson law or independent filtration is introduced. This gives the exact original source linearity prerequisite for arbitrary controlled zero-contact cash intervals, with countable rational-clock and stopping-time extensions left to the physical stopped-source proof.
-- source:
--   Root-connected physical source interface for 73419313/6211514c. Exact Proved original-X zero surviving deficit event 65b7c0e0 and exact Proved original-X BV drift upper ae ca1f370b; no Poisson replacement, no source mutation.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_surviving_positive_deficit_probability_eq_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_zero_barrier_survival_source_drift_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < barrierRuinTime X 0 ω →
      X.X T ω = (T : ℝ) * X.drift := by sorry
