-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_second_moment_ordered_pairs
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_second_moment_ordered_pairs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:12:46.787195+00:00
-- url     : https://prove2.me/theorems/1a119044-1fbc-474d-8506-13fd92e0e777
-- title:
--   Original source marked-jump second moment reduces exactly to ordered pair L1
-- statement:
--   On the original Levy path, given only first-moment integrability of its actual finite-band marked jump count, its second moment is integrable if and only if the genuine ordered source pair count is L1. The second moment expectation decomposes into the source first count plus twice the chronological pair expectation. No independent Poisson or new second-moment assumptions.
-- source:
--   The original source pathwise real factorial pair identity 074f945f and finite source times e5e6f70b.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_second_moment_ordered_pairs
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : Ω → ℝ := fun ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal
    let K : Ω → ℕ := fun ω =>
      ((F ω ×ˢ F ω).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
    Integrable J P →
    (Integrable (fun ω => (J ω) ^ 2) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, (J ω) ^ 2 ∂P) =
      (∫ ω, J ω + 2 * (K ω : ℝ) ∂P) := by sorry
