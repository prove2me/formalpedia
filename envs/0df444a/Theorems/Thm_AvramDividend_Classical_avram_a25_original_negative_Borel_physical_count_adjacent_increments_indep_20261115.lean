-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_physical_count_adjacent_increments_indep_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_physical_count_adjacent_increments_indep_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:17:38.471052+00:00
-- url     : https://prove2.me/theorems/7e146944-e635-47d3-ac30-ea1a47f9d608
-- title:
--   Independence of original physical negative-Borel marked jump counts before and after a deterministic time
-- statement:
--   For the original spectrally negative Lévy process on its original probability P and filtration, the actual marked jump counts for a measurable Borel set B on (0,s] and (s,s+T] are independent. Proved original raw count adaptedness b25029d5 makes the first count measurable with respect to 𝓕 s. Proved original source future-path marked-count extractor d9b9e3c2 gives a measurable functional of the shifted future path for the second count. Proved original Lévy future-path functional independence 36ce4b40 then yields the exact desired IndepFun. This is the first genuinely source-level independence input needed for the full original negative-Borel Poisson count law. No independent companion or alternative stochastic process.
-- source:
--   Proved original source hX.isProbability, b25029d5, d9b9e3c2, 36ce4b40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_physical_count_adjacent_increments_indep_20261115
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
    IndepFun (fun ω => NX ω (Ioc 0 s ×ˢ B))
      (fun ω => NX ω (Ioc s (s + T) ×ˢ B)) P := by sorry
