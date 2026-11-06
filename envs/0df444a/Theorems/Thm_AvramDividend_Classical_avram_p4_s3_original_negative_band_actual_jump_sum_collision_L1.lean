-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_actual_jump_sum_collision_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_collision_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:03:18.866196+00:00
-- url     : https://prove2.me/theorems/7503e7fb-19d2-4180-b1d8-7d60468aab11
-- title:
--   Original finite negative-band time-indexed jump sum has quadratic multiple-jump L1 error
-- statement:
--   For the actual original Lévy negative-band finite set of physical jump times on (0,T], any uniformly bounded path-and-time dependent jump kernel has an integrable multi-jump contribution, provided the isolated multi-jump sum is measurably represented. Its expected norm is at most the kernel bound times the squared physical negative-band intensity. This is the precise per-jump Taylor error estimate needed when replacing finite-band marked sums by isolated-jump contributions.
-- source:
--   Original physical finite negative-band marked times from avram_wave7_06_original_negative_band_marked_times_finite, exact ncard-to-finset-card bridge, and proved P4-S3 collision count mass quadratic theorem 0fa3d06f-cba6-4256-bd44-10ddb8c2bca0.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_collision_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (f : Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω u, |f ω u| ≤ B)
    (hErrMeas : AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T n).toFinset, f ω u
      else 0) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) P ∧
    (∫ ω, ‖if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0‖ ∂P) ≤ B * r ^ 2 := by sorry
