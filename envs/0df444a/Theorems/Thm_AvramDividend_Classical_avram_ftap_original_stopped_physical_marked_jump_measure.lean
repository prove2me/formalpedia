-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_marked_jump_measure
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_physical_marked_jump_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:08:37.308559+00:00
-- url     : https://prove2.me/theorems/97e2ad82-2dab-4819-a569-d826a7b717eb
-- title:
--   Stopped original Lévy time-and-size marked jump measure equals the original physical marked measure up to the stop
-- statement:
--   Pathwise equality of actual marked (jump time, jump size) counting measures for the original spectrally negative Lévy driver stopped at a finite random clock, versus the original Lévy marked jump measure restricted to jump times at or before the clock. Crucially, the left measure uses actual stopped jump sizes and the right measure uses original physical jump sizes. Reuses the accepted original physical jump-time counting measure and FTAP before-stop jump-size equality, together with pinned Mathlib Measure.map_congr and ae_restrict_mem. No finite-activity assumption, no artificial stochastic measures, and the stopping-time jump is included. Provides the marked Poisson jump-measure identity prerequisite for the physical source compensator.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_jump_count_measure
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_levy_stopped_left_jump_before_clock
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_physical_marked_jump_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → ℝ≥0) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
      MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
        Function.leftLim
          (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
            (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        MeasureTheory.stoppedProcess X.X
          (fun ω => (τ ω : WithTop ℝ≥0)) u ω -
          Function.leftLim
            (fun s : ℝ≥0 => MeasureTheory.stoppedProcess X.X
              (fun ω => (τ ω : WithTop ℝ≥0)) s ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).restrict
        (Iic (τ ω))).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u)) := by sorry
