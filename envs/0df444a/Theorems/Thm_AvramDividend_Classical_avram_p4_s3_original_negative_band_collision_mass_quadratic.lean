-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_collision_mass_quadratic
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_mass_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:19:58.075538+00:00
-- url     : https://prove2.me/theorems/0fa3d06f-cba6-4256-bd44-10ddb8c2bca0
-- title:
--   Original negative-band expected collision count is quadratic in the finite-band intensity
-- statement:
--   For the actual original Lévy path, the expected number of separated negative-band jumps on paths containing two or more such jumps is at most the square of the exact time-band intensity. This weighted O(T²) collision control helps bound finite-grid predictable compensation errors.
-- source:
--   Original-source band factorial moment 0a13392f-85cb-4eda-8293-758dc8d8a2a7, original count-cardinality bridge and measurability, and K*1_{K>=2} <= K(K-1).

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_collision_mass_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P) ≤ r ^ 2 := by sorry
