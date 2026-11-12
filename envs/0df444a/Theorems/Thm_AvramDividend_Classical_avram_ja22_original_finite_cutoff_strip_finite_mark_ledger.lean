-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_cutoff_strip_finite_mark_ledger
-- name    : AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_finite_mark_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:23:34.035852+00:00
-- url     : https://prove2.me/theorems/05e83481-d403-43d7-9995-85478d370451
-- title:
--   Original two cutoff intrinsic residual difference equals signed finite jump ledger
-- statement:
--   Express the difference of two original intrinsic residual cutoffs exactly as the difference of two compensated finite marked-jump sums on that sample path, preserving the pathwise jump-amplitude marks.
-- source:
--   J-A22 sound precursor for original finite-strip signed-mark L2 isometry. Proved 2c95a423 and 8a238662.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_finite_mark_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (t : ℝ≥0) (ω : Ω) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    ∃ (F G : Finset ℝ≥0),
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        -1 < j u ∧ j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∀ u : ℝ≥0, u ∈ G ↔ 0 < u ∧ u ≤ t ∧
        -1 < j u ∧ j u ≤ -(1 / ((m : ℝ) + 1))) ∧
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
        avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω =
          ((∑ u ∈ G, j u) -
            (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
              (-(1 / ((m : ℝ) + 1))), z ∂X.ν)) -
          ((∑ u ∈ F, j u) -
            (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
              (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by sorry
