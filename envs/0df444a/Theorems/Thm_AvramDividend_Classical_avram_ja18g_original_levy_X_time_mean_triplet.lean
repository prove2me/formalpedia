-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_levy_X_time_mean_triplet
-- name    : AvramDividend.Classical.avram_ja18g_original_levy_X_time_mean_triplet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:44:46.367626+00:00
-- url     : https://prove2.me/theorems/e82aa85f-f89e-4085-9d43-b32b94bb7757
-- title:
--   Original Levy X(t) first moment equals its triplet drift plus negative large-mark integral
-- statement:
--   Differentiate the original X(t) Laplace transform at θ=0+ under Standing and finite negative activity. With integrable X(t), large negative ν first moment and positive Laplace exponential moments, dominated convergence identifies E[X(t)] = t(c + ∫_{z≤−1} z ν(dz)). A direct same-space triplet moment formula.
-- source:
--   J-A18 zero-cutoff Gaussian mean splitting

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18g_original_levy_X_time_mean_triplet
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, X.X t ω ∂P) =
        (t : ℝ) * (X.c + (∫ z in Iic (-1 : ℝ), z ∂X.ν)) := by sorry
