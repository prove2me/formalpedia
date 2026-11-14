-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
-- name    : AvramDividend.Classical.avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T08:22:27.630454+00:00
-- url     : https://prove2.me/theorems/5687dc34-8ab3-4431-996d-e4014728ae79
-- title:
--   Original cutoff residual orthogonal to physically retained compensated small marks
-- statement:
--   On the original Levy-process probability space, the cutoff residual, consisting of the Gaussian component and omitted compensated small negative marks, is L2-orthogonal to the physically retained compensated negative band. Both are evaluated on the same sample path, with no false independence of the zero-cutoff residual and retained marks.
-- source:
--   Original-space Levy-Ito Gaussian/marked Poisson orthogonality using disjoint negative mark bands; source split and physical retained strip variance already Proved. The essential remaining ingredient for original self-covariance d376c1db.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_cutoff_residual_retained_band_cross_zero_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      let Rn : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω
      let Jn : Ω → ℝ := fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω
      Integrable (fun ω => Rn ω * Jn ω) P ∧
        (∫ ω, Rn ω * Jn ω ∂P) = 0 := by sorry
