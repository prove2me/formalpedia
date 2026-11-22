-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_levy_physical_jump_support
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_levy_physical_jump_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:51:36.263915+00:00
-- url     : https://prove2.me/theorems/0ebd626b-5d4b-4511-8be2-f2e03410fd94
-- title:
--   Physical nonzero left jumps of original stopped Lévy driver are exactly original jumps through the stop
-- statement:
--   For any original spectrally negative Lévy driver, physical jump size, and possibly infinite stopping clock, the stopped driver has a nonzero left jump at t iff t is no later than the stop and the original driver has a nonzero left jump at t. Reuses the two accepted adaptations of the full FTAPTheorem42/Foundations/Paths.lean left-jump stopping proof (at/before stop and strictly after) without additional assumptions. This exact support characterisation underpins stopped negative-jump measure and marked finite-mesh counting.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_before_clock
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_zero_after_clock
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_levy_physical_jump_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0) :
    (MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t ≠ 0) ↔
      (t : WithTop ℝ≥0) ≤ τ ω ∧
        (X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0) := by sorry
