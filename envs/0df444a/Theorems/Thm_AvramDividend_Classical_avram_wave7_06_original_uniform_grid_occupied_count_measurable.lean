-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_uniform_grid_occupied_count_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:26:34.50982+00:00
-- url     : https://prove2.me/theorems/8cd177de-23fe-4fb7-94d1-4cd0afeecdfd
-- title:
--   Actual Lévy negative-band uniform-grid occupied count is measurable
-- statement:
--   A finite sum over equal-width cells of actual original process X marked negative-jump occupancy indicators is measurable on original sample space. This instantiates measurable-grid K_m in the source dominated-convergence slope bridge.
-- source:
--   W7-06 original marked pathwise count from already ACCEPTED source cell indicator measurability bc862522. No auxiliary Poisson process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave7_06_original_uniform_grid_occupied_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (δ : ℝ≥0) (n m : ℕ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range m,
        ({ω : Ω | NX ω
          (Ioc ((i : ℝ≥0) * δ) ((i : ℝ≥0) * δ + δ) ×ˢ
            Iic (-(1 / ((n : ℝ) + 1)))) ≠ 0}).indicator
          (fun _ => (1 : ENNReal)) ω) := by sorry
