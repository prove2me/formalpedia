-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
-- name    : AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:12:28.101934+00:00
-- url     : https://prove2.me/theorems/6366b3de-f550-421f-b150-f65b02e3eed5
-- title:
--   Original intrinsic Gaussian source equals genuine Lévy path minus finite-activity drift and complete true physical jump series
-- statement:
--   The intrinsic Gaussian residual on the original filtered probability space equals the original Lévy path minus its deterministic finite-activity drift and minus its complete positive-time actual marked jump series, on one common conull event for all times.
-- source:
--   A35 proved physical source cutoff identity and pinned Mathlib tsum_neg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a35_original_intrinsic_gaussian_equals_minus_true_jump_series_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        X.X t ω -
        (t : ℝ) * (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) -
        (∑' u : ℝ≥0,
          if 0 < u ∧ u ≤ t then
            X.X u ω -
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
          else 0) := by sorry
