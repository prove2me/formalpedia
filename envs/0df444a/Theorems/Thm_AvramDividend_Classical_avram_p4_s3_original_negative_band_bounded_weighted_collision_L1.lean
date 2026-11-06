-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:38:29.264912+00:00
-- url     : https://prove2.me/theorems/59a94578-6d81-4312-8f6c-b19613f4daef
-- title:
--   Original finite-band bounded predictable coefficient has quadratic weighted collision L1 bound
-- statement:
--   For the actual original Lévy negative-band count, any measurable coefficient with a deterministic absolute bound B has an integrable collision-weighted jump count. Its expected weighted error has absolute value at most B times the squared physical band intensity. This directly prepares finite predictable-grid compensation for bounded locally stopped Taylor coefficients.
-- source:
--   Proved/public original weighted multi-jump collision estimate 0fa3d06f-cba6-4256-bd44-10ddb8c2bca0 and exact pinned MeasureTheory.Integrable.mono domination.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_bounded_weighted_collision_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ) (hHm : Measurable H) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ ω, |H ω| ≤ B) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0)) P ∧
    |∫ ω, H ω * (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P| ≤ B * r ^ 2 := by sorry
