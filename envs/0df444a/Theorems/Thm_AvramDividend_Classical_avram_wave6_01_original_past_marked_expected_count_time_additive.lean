-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_time_additive
-- name    : AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_time_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:06:14.566681+00:00
-- url     : https://prove2.me/theorems/0b578fb5-f213-4b6d-b777-a4c49655d5da
-- title:
--   Original expected past-restricted marked jump count is exactly additive in physical time
-- statement:
--   For any original SpectrallyNegativeLevy and arbitrary F_s event A and Borel mark set B, the expectation of the literal same-path intrinsic count in (s,t] splits exactly as the sum of expectations on adjacent (s,u] and (u,t], without BV, finite activity, σ-finite intensity, Poisson proxy, compensation hypothesis or identity with ν(B). This supplies a source-faithful additive-time functional necessary to identify the physical Lévy mark rate.
-- source:
--   Use Proved exact pathwise source time slicing 5658e787; s-finite original sample kernel eb357 gives measurability of the earlier subinterval count; lintegral_add_left then preserves additivity after restricting to genuine past event A.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_time_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ B) ∂P) =
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s u ×ˢ B) ∂P) +
    (∫⁻ ω in A,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc u t ×ˢ B) ∂P) := by sorry
