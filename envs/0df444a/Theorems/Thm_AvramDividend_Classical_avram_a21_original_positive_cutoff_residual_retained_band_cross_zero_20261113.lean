-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
-- name    : AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T08:55:36.672196+00:00
-- url     : https://prove2.me/theorems/d1275acc-9d16-4d23-a20b-20a6c68b8879
-- title:
--   Positive-cutoff physical residual is orthogonal to physically retained compensated negative band
-- statement:
--   For every strictly positive cutoff index on the original Levy process sample space, the Gaussian plus omitted negative small-band residual is L2 orthogonal to the physically retained compensated negative marked-jump band. This isolates the nontrivial part of physical source orthogonality after n=0 is proved.
-- source:
--   Original physical Levy-Ito disjoint Gaussian and Poisson marked-band orthogonality; cutoff n=0 proved separately, positive cutoff remains the substantive missing source part.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_positive_cutoff_residual_retained_band_cross_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let R : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X (n + 1) t ω
      let J : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X (n + 1) t ω
      Integrable (fun ω => R ω * J ω) P ∧
        (∫ ω, R ω * J ω ∂P) = 0 := by sorry
