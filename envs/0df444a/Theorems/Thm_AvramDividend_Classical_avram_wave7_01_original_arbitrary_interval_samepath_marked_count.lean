-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_interval_samepath_marked_count
-- name    : AvramDividend.Classical.avram_wave7_01_original_arbitrary_interval_samepath_marked_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:49:11.726624+00:00
-- url     : https://prove2.me/theorems/ed946858-6ec2-4644-ae4a-b8106a86a25b
-- title:
--   Original arbitrary marked rectangle equals intrinsic count of the same shifted future path
-- statement:
--   On each original sample ω, the literal marked jump measure of SpectrallyNegativeLevy X on physical interval (s,t] with an arbitrary Borel mark set B equals the count of true nonzero jumps of the actual shifted increment path at relative times (0,t−s]. This is exact pointwise transport for any s≤t without a proxy process or finite activity. It does not claim measurability of the path-count functional or that its expected measure equals (t−s)ν(B).
-- source:
--   Already Proved original source time clock and mark transport b1721778-5db9-4e5b-96a0-c3d000566015; specialise its relative horizon to t−s and rewrite s+(t−s)=t.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_arbitrary_interval_samepath_marked_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ t - s ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard := by sorry
