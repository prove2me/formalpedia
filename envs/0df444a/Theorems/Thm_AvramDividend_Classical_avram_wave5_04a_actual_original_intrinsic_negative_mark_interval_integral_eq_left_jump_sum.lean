-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:06:37.497936+00:00
-- url     : https://prove2.me/theorems/e40a85f1-31c7-4d8a-b66e-a0bd93a1554b
-- title:
--   Actual original Lévy intrinsic negative-mark interval integral equals all actual source left-jump magnitudes
-- statement:
--   For every sample path of the actual original spectrally negative Levy process, and every nonnegative real time interval (s,t], the negative-mark magnitude integral against the genuine intrinsic source counting measure equals exactly the unrestricted extended-real sum over all actual original-source left jumps. The positive-time nonzero-mark restriction disappears because zero jumps and positive marks contribute zero; this is a pathwise identity, requiring neither bounded variation nor a separate Poisson model. It makes the BV residual's intrinsic jump series directly interchangeable with the genuine source jump measure.
-- source:
--   Chat04-A original-path specialisation of canonically Proved actual intrinsic jump counting measure generic kernel identity e4542c93-c64b-453a-b582-e5ec26265dfc. No independent stochastic noise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Pathwise identity: the actual source intrinsic negative-mark integral
on an interval is precisely the all-time sum of its genuine negative
left-jump magnitudes. No Poisson representation is introduced. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_original_intrinsic_negative_mark_interval_integral_eq_left_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) :
    (∫⁻ p,
      (if s < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' (u : ℝ≥0),
      if s < u ∧ u ≤ t then
        ENNReal.ofReal
          (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0 := by sorry
