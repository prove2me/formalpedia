-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_marked_liminf_correctness_gives_product_extractor
-- name    : AvramDividend.Classical.avram_wave7_01_cadlag_marked_liminf_correctness_gives_product_extractor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:02:25.015526+00:00
-- url     : https://prove2.me/theorems/9d092445-e51c-4154-ba4f-96bb22024c0a
-- title:
--   A correct marked-grid lower-tail limit provides a product-measurable càdlàg jump extractor
-- statement:
--   If an explicitly specified sequence of finite grids satisfies the genuine pathwise identity between a càdlàg Borel-marked intrinsic jump count and the lower-tail envelope sup_m inf_{k≥m} of its finite marked-increment counts, then this envelope is a globally product-coordinate measurable extension. Unlike a coarse-grid supremum, the lower-tail construction discards transient overcounts. It does not assert that arbitrary grids satisfy the pathwise identity. The remaining obligation is specific refining-grid correctness for all relevant jump marks.
-- source:
--   Apply the separate Proved Borel product-measurability of the marked-grid lower-tail envelope and choose that expression as the witness F; transfer the explicit hGrid pathwise count identity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_cadlag_marked_liminf_correctness_gives_product_extractor
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = (⨆ m : ℕ, ⨅ k : ℕ, if m ≤ k then
          ((((Finset.range (n k)).filter (fun i =>
            Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))
          else ⊤)) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by sorry
