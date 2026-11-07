-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_marked_rectangle
-- name    : AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_marked_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T19:21:55.777051+00:00
-- url     : https://prove2.me/theorems/624daffe-f11b-436f-acee-6ff31d5ef1b2
-- title:
--   Original intrinsic marked jump rectangles preserved exactly by freezing after finite prefix
-- statement:
--   For the actual original Lévy path, freezing at deterministic n preserves every strictly positive-time jump mark in (0,n], hence the exact marked counting measures agree on each Borel mark rectangle. The time-zero atom and endpoint n are treated exactly.
-- source:
--   Direct consequence of Proved source left-limit frozen identity 8e873bf7 on positive u≤n, plus measure-map and count restrictions; supplies rectangular hypothesis to Proved weighted-mark transport 68109213 to close frozen weighted cutoff 40f97b15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_original_frozen_prefix_marked_rectangle
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X (min u (n : ℝ≥0)) ω -
        Function.leftLim (fun v : ℝ≥0 => X.X (min v (n : ℝ≥0)) ω) u)))
      (Ioc 0 (n : ℝ≥0) ×ˢ B) := by sorry
