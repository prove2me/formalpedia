-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_monotone_mark_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_monotone_mark_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:13:25.710688+00:00
-- url     : https://prove2.me/theorems/ef56e8b2-e6ab-4abd-878f-b994dc9d249d
-- title:
--   Continuity from below of genuine original Lévy marked jump counts on increasing Borel bands
-- statement:
--   The true original pathwise marked jump count on an increasing union of mark sets is the supremum of the individual counts. This property requires neither finite activity nor ν-intensity.
-- source:
--   Mathlib Monotone.measure_iUnion; original intrinsic marked jump measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_monotone_mark_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ℕ → Set ℝ)
    (hMono : Monotone B) :
    ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ n, B n)) =
      ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B n)) := by sorry
