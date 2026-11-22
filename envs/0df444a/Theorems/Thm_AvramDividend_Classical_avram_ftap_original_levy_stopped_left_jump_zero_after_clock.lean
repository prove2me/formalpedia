-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_zero_after_clock
-- name    : AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_zero_after_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T12:47:35.471779+00:00
-- url     : https://prove2.me/theorems/28cb952a-e18c-42cf-a87c-9973eabf5168
-- title:
--   Original stopped Lévy driver has no physical jumps strictly after the stopping clock
-- statement:
--   For any physical time t strictly after a finite stopping clock τ, the actual stopped Lévy driver remains constant in a left neighbourhood of t and thus has zero left jump. This directly adapts FTAPTheorem42/Foundations/Paths.lean processLeftJump_stoppedProcess_eq_zero_of_lt, including the source's Ico_mem_nhdsLT argument and exact extended-time coercions. It proves the zero-jump-after-stop half needed for physical stopped jump counting.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_levy_stopped_left_jump_zero_after_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) (t : ℝ≥0)
    (ht : τ ω < (t : WithTop ℝ≥0)) :
    MeasureTheory.stoppedProcess X.X τ t ω -
      Function.leftLim
        (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X τ s ω) t =
      0 := by sorry
