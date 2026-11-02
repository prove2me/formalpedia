-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_interval_source_budget
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_interval_source_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:22:23.067085+00:00
-- url     : https://prove2.me/theorems/d7afa88a-9b07-4cae-8003-64db2aac4b99
-- title:
--   Real original intrinsic negative-mark interval source loss is bounded by actual BV drift residual
-- statement:
--   For a genuine original bounded-variation spectrally negative Levy sample path, on one common probability-one event, the real value of its intrinsic negative-mark source counting-measure integral over every ordered interval is nonnegative and no larger than elapsed drift minus the actual process increment. Uses the canonical monotone nonnegative residual to certify the real inequality, not just an extended-real domination. It is an original-process source magnitude budget suitable for stopped C1 chain-rule estimates; no Poisson replacement, pure-jump equality or controlled Ito-Meyer is assumed.
-- source:
--   Chat04-A deduction from Proved original BV source exact interval decomposition c4b53c7c-d769-4894-a0d8-c0b2a1516d1e and independently Proved original source measure integral-to-jump equality e40a85f1-31c7-4d8a-b66e-a0bd93a1554b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every true original BV source intrinsic negative-mark measure
increment is a nonnegative real and is dominated by physical drift
less the actual source increment on one common almost-sure event. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_intrinsic_negative_mark_measure_real_interval_source_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      let J : ℝ :=
        (∫⁻ p,
          (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal
      0 ≤ J ∧
        J ≤ ((t : ℝ) - (s : ℝ)) * X.drift -
          (X.X t ω - X.X s ω) := by sorry
