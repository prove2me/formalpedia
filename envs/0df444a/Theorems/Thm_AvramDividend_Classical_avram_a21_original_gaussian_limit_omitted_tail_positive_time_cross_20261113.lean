-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_omitted_tail_positive_time_cross_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_time_cross_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T09:28:51.302988+00:00
-- url     : https://prove2.me/theorems/f4cfb5db-a9b1-4cb8-9068-fc2a3edbae94
-- title:
--   Original Gaussian limit is orthogonal to omitted negative mark tails at positive horizon
-- statement:
--   At every strictly positive horizon and every cutoff, the original path Gaussian-limit process is L2-orthogonal to the physically omitted negative mark tail on the same probability space. Requires direct source disjoint Gaussian/jump orthogonality. Zero-horizon case separately Proved.
-- source:
--   Original Levy-Ito decomposition, Gaussian component orthogonality to independent omitted negative marked jump increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_omitted_tail_positive_time_cross_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    ∀ (n : ℕ) (t : ℝ≥0), 0 < t →
      (∫ ω, R t ω *
        (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω) ∂P) = 0 := by sorry
