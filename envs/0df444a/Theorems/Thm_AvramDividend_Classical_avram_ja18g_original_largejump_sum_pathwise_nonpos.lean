-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_sum_pathwise_nonpos
-- name    : AvramDividend.Classical.avram_ja18g_original_largejump_sum_pathwise_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:48:00.278426+00:00
-- url     : https://prove2.me/theorems/a7ec5d45-dcfb-4b79-a748-6bd6a3d49f5d
-- title:
--   Original large-negative-jump sum is nonpositive pathwise
-- statement:
--   Each original jump mark in Iic(-1) is negative; hence the real integral defining the physical large-negative-jump sum is nonpositive for every time and sample path. Supports the signed Campbell mean conversion without any auxiliary process.
-- source:
--   J-A18 original Gaussian zero-cutoff mean splitting

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_largejump_sum_pathwise_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (t : ℝ≥0) (ω : Ω),
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ≤ 0 := by sorry
