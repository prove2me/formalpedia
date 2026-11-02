-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jumpmark_vanish_from_left
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:34:43.83887+00:00
-- url     : https://prove2.me/theorems/7b213676-7019-4022-b899-1e1a2969a005
-- title:
--   Actual original Lévy jump marks vanish as jump times approach a positive clock from the left
-- statement:
--   For every original SpectrallyNegativeLevy sample path and every positive time t, the genuine intrinsic jump-size function ΔX(u) converges to zero as u approaches t strictly from below. No assumption of bounded variation, finite Lévy intensity, Marked-Poisson representation, new filtration or almost-sure modification is needed. This is a precise local truncation fact: for any positive threshold, sufficiently late pre-t source jumps have marks smaller than that threshold.
-- source:
--   Pinned source X.leftLim and Mathlib continuousWithinAt_leftLim_Iic, nhdsWithin_mono, Tendsto.sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_jumpmark_vanish_from_left
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      (𝓝[<] t) (𝓝 (0 : ℝ)) := by sorry
