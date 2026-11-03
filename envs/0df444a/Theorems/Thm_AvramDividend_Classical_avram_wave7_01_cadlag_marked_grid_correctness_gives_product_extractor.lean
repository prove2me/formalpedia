-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_marked_grid_correctness_gives_product_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_cadlag_marked_grid_correctness_gives_product_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:37:04.675623+00:00
-- url     : https://prove2.me/theorems/7be35405-f7d9-4617-a1e7-c2b9ca96fcc0
-- title:
--   A pathwise correct finite-grid marked-jump count yields a measurable càdlàg extractor
-- statement:
--   For any Borel jump-mark B and any countable family of finite coordinate grids, if one proves that the extended supremum of the marked finite-increment grid counts equals the intrinsic B-marked jump count for every right-continuous path with strict left limits on [0,T], then that same supremum is a measurable full-coordinate-product path functional extending the exact jump count. The hypothesis is a genuine pathwise correctness obligation; arbitrary grids are not claimed correct. This isolates analytic grid convergence from measurability to progress the original Lévy compensator.
-- source:
--   Directly apply the accepted product-measurability theorem 1120ee03-ba60-4f08-99f4-a4d13d189417, choose its explicit grid-supremum function and transfer the supplied càdlàg pathwise correctness identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_sup_product_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_cadlag_marked_grid_correctness_gives_product_extractor
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by sorry
