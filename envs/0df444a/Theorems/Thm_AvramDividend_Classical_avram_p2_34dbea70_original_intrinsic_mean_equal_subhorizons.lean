-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_equal_subhorizons
-- name    : AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_equal_subhorizons
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:01:44.217709+00:00
-- url     : https://prove2.me/theorems/85b19ac7-7bc9-4d6f-afac-2a83bbf6246d
-- title:
--   Original intrinsic marked jump-count mean partitions into equal subhorizons
-- statement:
--   For any strictly positive integer n, real nonnegative horizon t, and measurable mark set B, the original-process expected intrinsic jump count on (0,t] is n times the expected count on (0,t/n]. This is the exact equal-partition consequence of the proved original stationary-horizon additive mean, without assuming a jump-rate formula, finite activity or compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_intrinsic_mean_integer_multiple_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_34dbea70_original_intrinsic_mean_equal_subhorizons {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (B : Set ℝ)
    (hB : MeasurableSet B) (t : ℝ≥0) (n : ℕ) (hn : n ≠ 0) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ B) ∂P) =
    n • (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 =>
        (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (t / (n : ℝ≥0)) ×ˢ B) ∂P) := by sorry
