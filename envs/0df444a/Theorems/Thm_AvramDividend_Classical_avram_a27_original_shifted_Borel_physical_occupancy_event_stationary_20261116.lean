-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
-- name    : AvramDividend.Classical.avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T09:18:54.222443+00:00
-- url     : https://prove2.me/theorems/439d7e09-1979-479d-988d-f9852bfa50f2
-- title:
--   Original physical negative-Borel occupancy event is stationary under time translation
-- statement:
--   For the actual original Lévy physical marked jump measure, the event that (s,s+T] contains any B-marked jump has exactly the same original P probability as the event that (0,T] does. Transfer the already Proved original stationary law of physical marked counts 37abf3aa through the measurable nonzero count event using Proved rectangle-count measurability 8146a449. No extra assumptions on finite intensity or independent copies.
-- source:
--   Proved original physical marked count stationary law 37abf3aa and original rectangle-count measurability 8146a449.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_shifted_Borel_physical_occupancy_event_stationary_20261116
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    P {ω : Ω | NX ω (Ioc s (s + T) ×ˢ B) ≠ 0} =
      P {ω : Ω | NX ω (Ioc 0 T ×ˢ B) ≠ 0} := by sorry
