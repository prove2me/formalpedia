-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise
-- name    : AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:37:08.963217+00:00
-- url     : https://prove2.me/theorems/2fb66bc6-8c4b-4f13-ada4-8487858c1a61
-- title:
--   Genuine Lévy jump-count continuity from below on nested future time-and-mark rectangles
-- statement:
--   For every original Lévy path, the intrinsic jump measure of an increasing union of rectangles with simultaneously increasing horizons and mark sets is the supremum of the original rectangle counts, without an intensity or finiteness assumption.
-- source:
--   Original SpectrallyNegativeLevy jump map, Mathlib Monotone.measure_iUnion and order of future time-mark products.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_original_joint_horizon_mark_iSup_pathwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (T : ℕ → ℝ≥0) (hT : Monotone T)
    (B : ℕ → Set ℝ) (hB : Monotone B) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (⋃ n, Ioc s (s + T n) ×ˢ B n) =
    ⨆ n, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T n) ×ˢ B n) := by sorry
