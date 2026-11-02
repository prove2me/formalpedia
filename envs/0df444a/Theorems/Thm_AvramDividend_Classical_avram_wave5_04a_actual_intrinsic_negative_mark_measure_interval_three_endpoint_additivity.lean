-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_negative_mark_measure_interval_three_endpoint_additivity
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_negative_mark_measure_interval_three_endpoint_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:40:50.019196+00:00
-- url     : https://prove2.me/theorems/72d6be0a-19e5-4d2a-8dbd-0e281a355370
-- title:
--   Genuine intrinsic original-source negative mark integral is exactly additive on ordered time intervals
-- statement:
--   For the actual spectrally negative Levy sample path and any ordered nonnegative times s≤t≤r, the complete genuine intrinsic source counting-measure integral of negative source left-jump magnitudes over (s,r] is exactly the sum of its integrals over (s,t] and (t,r]. This is a pathwise extended-real measure identity valid with infinite jump activity, not an expectation, a compensated integral, or an independent Poisson model. It strengthens the original-process BV source decomposition's stopped interval interface.
-- source:
--   Chat04-A combines the dedicated pathwise intrinsic original-source negative-mark integral-to-jump sum identity and actual original negative-jump three-endpoint series additivity; no stochastic compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_negative_jump_magnitude_three_endpoint_interval_additivity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The true intrinsic source negative-mark integral is finitely
additive on consecutive original time intervals, pathwise. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_negative_mark_measure_interval_three_endpoint_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) +
    (∫⁻ p,
      (if t < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
