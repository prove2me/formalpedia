-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_jump_count_measure
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_physical_jump_count_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:04:36.957072+00:00
-- url     : https://prove2.me/theorems/8fb07c9e-63df-496d-96c1-dedd7b4c0bdd
-- title:
--   Original stopped Lévy physical jump counting measure equals original jump counting measure restricted through stop
-- statement:
--   For any original spectrally negative Lévy process and arbitrary finite random clock τ, the counting measure on its nonzero physical stopped jump times t>0 exactly equals the original nonzero physical jump-time counting measure restricted to t≤τ(ω), path by path. This is a genuine measure identity, not merely an event support implication, and explicitly includes the stopping-time jump. It combines the accepted source-faithful FTAP Foundations/Paths stopped left-jump equivalence with restriction-of-measure intersection identity. It is the physical-time counting measure bridge for original stopped Poisson marked jumps, with no extra assumption of finite jump activity.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_levy_physical_jump_support
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_physical_jump_count_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}) =
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).restrict
      (Iic (τ ω)) := by sorry
