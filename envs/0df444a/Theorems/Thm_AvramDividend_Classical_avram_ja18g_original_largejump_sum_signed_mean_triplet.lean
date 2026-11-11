-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_sum_signed_mean_triplet
-- name    : AvramDividend.Classical.avram_ja18g_original_largejump_sum_signed_mean_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:44:47.707896+00:00
-- url     : https://prove2.me/theorems/0ef55719-ab95-46e7-9474-f3768e12c376
-- title:
--   Original physical large-negative-jump sum has signed Campbell mean
-- statement:
--   Under Standing and the proved large negative mark first moment, integrate the actual same-sample-space large-jump sum against P. The original signed Campbell identity gives E[J_t] = t∫_{z≤−1} z ν(dz), preserving actual time and negative-jump endpoint.
-- source:
--   J-A18 zero-cutoff Gaussian mean splitting

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_largejump_sum_signed_mean_triplet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
        (t : ℝ) * (∫ z in Iic (-1 : ℝ), z ∂X.ν) := by sorry
