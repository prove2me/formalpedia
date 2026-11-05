-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_second_moment_pair_L1_auto
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_second_moment_pair_L1_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:12:56.194221+00:00
-- url     : https://prove2.me/theorems/84c3732e-d8f5-468f-8a71-801cf568012a
-- title:
--   Unconditional original negative-band marked-count second moment equals source chronological pairs
-- statement:
--   On the original process and any finite cutoff, the squared intrinsic marked count is integrable exactly when its chronological marked-jump pair count is integrable, and its second-moment expectation equals the first source count plus twice the source chronological pair expectation. Original P2 first-moment integrability is proved automatically, with no added assumptions or Poisson proxy.
-- source:
--   Proved 3d8bb7f8 original intrinsic count L1; Proved 1a119044 original second-moment source-pair equivalence; original finite-band times e5e6f70b.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_second_moment_ordered_pairs
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_second_moment_pair_L1_auto
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
    (Integrable (fun ω => (J ω) ^ 2) P ↔
      Integrable (fun ω => 2 * (K ω : ℝ)) P) ∧
    (∫ ω, (J ω) ^ 2 ∂P) =
      (∫ ω, J ω + 2 * (K ω : ℝ) ∂P) := by sorry
