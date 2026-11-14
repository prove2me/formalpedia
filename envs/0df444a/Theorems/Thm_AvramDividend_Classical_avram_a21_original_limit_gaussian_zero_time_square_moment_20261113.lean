-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
-- name    : AvramDividend.Classical.avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:21:32.6941+00:00
-- url     : https://prove2.me/theorems/ef291df3-1610-4caf-a1cf-5320d9baa758
-- title:
--   Physical original intrinsic Gaussian limit has exact zero-time L2 norm
-- statement:
--   At source time zero, the original almost-sure cutoff residual limit is zero. Hence its square is integrable and its second moment is zero. The underlying physical zero-time limit is already Proved; this is the zero-time boundary for the open Gaussian-limit second moment.
-- source:
--   Proved 4f4d81f6 original residual limit zero-time theorem; elementary integrable zero and ae integral equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_limit_gaussian_zero_time_square_moment_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k T ω)
        atTop (nhds (R T ω))) :
    Integrable (fun ω => (R 0 ω) ^ 2) P ∧
      (∫ ω, (R 0 ω) ^ 2 ∂P) = 0 := by sorry
