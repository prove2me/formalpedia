-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
-- name    : AvramDividend.Classical.avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:45:31.610863+00:00
-- url     : https://prove2.me/theorems/41bfd2c8-f85d-403a-b1c4-2dc56d94a83a
-- title:
--   Every finite-horizon càdlàg Borel-marked jump count admits a coordinate-product measurable extension
-- statement:
--   For a finite horizon T and arbitrary Borel set B of real jump sizes, the extended-natural cardinality of nonzero path jumps of size in B on (0,T] is a measurable functional of the full real-valued coordinate path, when restricted to all right-continuous paths with finite strict-left limits. The functional is defined measurably on the entire product-coordinate measurable space, including arbitrary non-cadlag paths, as a Borel extension. This is the missing sigma-algebra/analytic grid-limit lemma for the exact original Lévy compensator; it is not an assumed Lévy rate or a replacement process.
-- source:
--   Classical càdlàg path-space Borel jump measure construction from rational-grid discontinuity detection; Mathlib product measurable pi and monotone finite marked-cell approximations. Requires a genuine proof of Borel marked jump extraction; no sorry/admit or closure axiom in submitted proofs.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_cadlag_arbitrary_borel_marked_jumps_product_measurable
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by sorry
