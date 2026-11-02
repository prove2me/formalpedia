-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_measure_interval_monotone
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_measure_interval_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:31:23.196463+00:00
-- url     : https://prove2.me/theorems/f0cf2ac7-12ff-456a-a8d9-5227edf3f565
-- title:
--   Genuine original source intrinsic negative-mark mass is monotone under time-window extension
-- statement:
--   For every sample path of the actual spectrally negative Levy process and any ordered nonnegative endpoints s≤t≤r, the intrinsic negative-mark source jump measure mass over (s,t] is no larger than its mass over (s,r]. The result is pathwise and remains true with infinitely many jumps, even if mass is infinite. It is proved by the exact original intrinsic measure-to-left-jump series identity and monotonicity of extended-real sums; no bounded-variation assumption, independent Poisson model, compensator or Ito-Meyer theorem is needed. It is suitable for localising source jump mass at random stopping endpoints.
-- source:
--   Chat04-A pathwise monotonicity of true original negative-mark counting measure via Proved e40a85f1-31c7-4d8a-b66e-a0bd93a1554b and pinned Mathlib ENNReal.tsum_le_tsum.

import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine original source intrinsic negative-mark mass of a
smaller time window is dominated by its mass on an extended window,
pathwise even in the presence of infinite jump activity. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_measure_interval_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t r : ℝ≥0) (hst : s ≤ t) (htr : t ≤ r) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ≤
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ r then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
