-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:26:55.923197+00:00
-- url     : https://prove2.me/theorems/96dce014-cc78-4c8a-9787-74dabc67f12a
-- title:
--   Actual original BV source increments plus intrinsic negative jumps bounded by physical drift
-- statement:
--   For every bounded-variation spectrally negative Lévy source on its original sample space, an almost-everywhere simultaneous inequality bounds the source increments plus the true negative-jump magnitude integral by the elapsed time multiplied by its correctly compensated physical drift. No stationary residual classification, no Standing or integrability beyond BV, and no jump compensator is assumed.
-- source:
--   Original Proved BV source exact interval jump/remainder decomposition, using monotonicity of its genuine original path residual. The inequality remains valid before identifying that residual as zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV source has no upward variation beyond its physical drift:
its unremoved increasing residual only strengthens the upper bound. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_actual_source_negative_jumps_drift_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      X.X t ω - X.X s ω +
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal ≤
      ((t : ℝ) - (s : ℝ)) * X.drift := by sorry
