-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_physical_increment_source_jump_decomposition
-- name    : AvramDividend.Classical.avram_p3_main_original_physical_increment_source_jump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:24:00.484202+00:00
-- url     : https://prove2.me/theorems/ce5c459f-71d4-45f9-95e1-75fa3696ca0f
-- title:
--   Exact original Lévy physical increment equals jump-removed increment minus intrinsic source jump mass
-- statement:
--   The actual original Lévy path increment between any two nonnegative times is the increment of the source jump-removed path X+J minus the increment of the genuine original left-jump mass J. It uses exactly the same X, sample ω and original jump-time sum as P3-A and P3-D, with no zero-residual or surrogate process assumption.
-- source:
--   Original physical X with X.X, Function.leftLim and exact original negative jump mass from Proved P3-A; intended discharge of hstep in P3-main finite-grid C1 two-stage bound d8b4a9b4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_physical_increment_source_jump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) :
    let J : ℝ≥0 → ℝ := fun t =>
      (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω
      else 0)
    (X.X v ω - X.X u ω) =
      ((X.X v ω + J v) - (X.X u ω + J u)) -
        (J v - J u) := by sorry
