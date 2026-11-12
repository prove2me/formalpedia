-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_cutoff_strip_exact_square_moment
-- name    : AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_exact_square_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T16:06:23.688937+00:00
-- url     : https://prove2.me/theorems/9a1c9ee4-676d-4f3f-a79c-644771754f94
-- title:
--   Original finite cutoff compensated strip has exact mark-square second moment
-- statement:
--   On the original filtered probability space prove finite-compensated-band L2 isometry for the difference of two intrinsic residual cutoffs; no limit or auxiliary Brownian variable.
-- source:
--   J-A22 physical noise strand, genuine finite-band Poisson covariance obligation for 1679c8a4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja22_original_finite_cutoff_strip_exact_square_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      Integrable (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2) P ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - avram_p4_h_gaussian_intrinsic_truncated_residual X m t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))), z ^ 2 ∂X.ν) := by sorry
