-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_futurepath_marked_count_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:39:39.9664+00:00
-- url     : https://prove2.me/theorems/b1721778-5db9-4e5b-96a0-c3d000566015
-- title:
--   Same-path original marked Lévy jump count equals shifted future-increment path jump count
-- statement:
--   For every original SpectrallyNegativeLevy P 𝓕 path, every deterministic start s, finite relative horizon T, and every Borel mark set B, the literal original marked jump measure N_X(ω)((s,s+T]×B) equals the exact cardinal count of genuine nonzero jumps of its own shifted increment path v↦X(s+v,ω)−X(s,ω) over v∈(0,T] with marks in B. Both sides use the same original ω and same source X. No probability-space replacement, equality-in-law substitution, filtration alteration, BV, or finite-activity assumption is used. This is the pathwise identification needed before the source future-path independence theorem can be applied to marked jump counts; marked source intensity ν(B) remains a separate obligation.
-- source:
--   Composes the source clock translation and strict-left future-increment translation to prove the precise same-path jump mark and count equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_shifted_future_source_leftLim_translation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_clock_translation
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_futurepath_marked_count_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard := by sorry
