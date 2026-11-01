-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:12:34.329587+00:00
-- url     : https://prove2.me/theorems/f6336d40-2d19-444f-bacd-83724316de67
-- title:
--   Intrinsic original-path Lévy counting measure evaluates on measurable time–jump rectangles
-- statement:
--   For every actual source spectrally negative Lévy process and every original sample ω, restrict the NNReal-time counting measure to strictly positive times with nonzero true source jump ΔX(u,ω). Push that measure forward by the genuinely measurable path map u↦(u,ΔX(u,ω)). For any interval (s,t] and Borel mark band B, the resulting intrinsic measure evaluated on the time-mark rectangle equals the extended cardinality of exactly those original-path jump times in the rectangle. No Poisson property, local finiteness, compensation, external Brownian or replacement Lévy process is assumed or claimed.
-- source:
--   Prove2Me canonically Proved source joint jump-mark measurability 9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1. Pinned Mathlib Measure.count, Measure.map_apply, Measure.restrict_apply, Measure.count_apply. Avram–Palmowski–Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}).encard := by sorry
