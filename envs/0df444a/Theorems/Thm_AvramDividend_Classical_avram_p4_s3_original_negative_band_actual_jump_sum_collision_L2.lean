-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_actual_jump_sum_collision_L2
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_collision_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:04:12.309622+00:00
-- url     : https://prove2.me/theorems/84881d4f-bc44-4790-a347-7e37c6187485
-- title:
--   Actual original negative-band physical jump-time sum has quadratic L2 collision error
-- statement:
--   For the original physical Lévy negative-band jump times on (0,T], any uniformly bounded time-indexed, path-dependent kernel has square-integrable multiple-jump contribution when its squared finite sum is measurable, with E[(sum restricted to K≥2)^2]≤2B²r². This supplies a direct L² finite-grid replacement error for the stopped Itô–Meyer source terms.
-- source:
--   Actual original finite marked times theorem e5e6f70b-a901-43ba-b2bc-56911d56899f and accepted original squared collision count cd66a508-bc7d-4574-8020-97d52db80c9a; finite sum norm triangle and a deterministic square bound.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_collision_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (f : Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω u, |f ω u| ≤ B)
    (hErrSquareMeas : AEStronglyMeasurable (fun ω =>
      (if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω T n).toFinset, f ω u
      else 0) ^ 2) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2) P ∧
    (∫ ω, (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2 ∂P) ≤
      2 * B ^ 2 * r ^ 2 := by sorry
