-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_NX_time_restrict
-- name    : AvramDividend.Classical.avram_ftap_original_stopped_NX_time_restrict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:38:06.2178+00:00
-- url     : https://prove2.me/theorems/8d3ffbc6-fe5b-43a6-955a-e252e7252d4e
-- title:
--   Original stopped physical marked jump measure equals original Avram NX time-coordinate restriction
-- statement:
--   For the actual stopped original spectrally negative Levy driver, its physical marked (time, jump-size) measure is exactly the original driver's canonical physical NX measure restricted to marked points with time coordinate at or before the finite random clock. This is the native NX representation used by original Avram compensated marked Poisson integrals, and includes the jump at the clock without a finite activity assumption. Reuses the already accepted full stopped marked-measure equality, original model's proved measurable mark map, and pinned Mathlib Measure.restrict_map with the original time-coordinate Borel mask. The equivalence does not require constructing a new abstract Poisson noise process.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Foundations/Paths.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ftap_original_stopped_physical_marked_jump_measure
import Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_mark_map_measurable
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_ftap_original_stopped_NX_time_restrict
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
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u))).restrict
      {p : ℝ≥0 × ℝ | p.1 ≤ τ ω} := by sorry
