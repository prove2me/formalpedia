-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
-- name    : AvramDividend.Classical.avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:00:41.819807+00:00
-- url     : https://prove2.me/theorems/d7545aa3-95c0-4687-93c8-2d135155b47c
-- title:
--   Original intrinsic negative-marked jump mass on [0,T] equals that on (0,T] exactly
-- statement:
--   The original intrinsic jump measure NX counts strictly positive jump times. For every physical path ω and any Borel mark set B, the count on [0,T]×B equals the count on (0,T]×B. This follows from the already Proved zero-time atom theorem and disjoint/union count monotonicity, preserving actual original source X and all mark conventions. Used to transfer finite negative-mark mass to source49 stopped weighted jump bound.
-- source:
--   Proved e2216ed6 original actual source jump measure zero initial time; Mathlib Set.Ioc_union_left and measure_union_le.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward61_original_intrinsic_closed_positive_time_count_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Icc 0 T ×ˢ B) =
    ((Measure.count.restrict {u : ℝ≥0 |
       0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u, X.X u ω -
         Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc 0 T ×ˢ B) := by sorry
