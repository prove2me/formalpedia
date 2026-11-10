-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
-- name    : AvramDividend.Classical.avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T13:54:20.730142+00:00
-- url     : https://prove2.me/theorems/4f4d81f6-e0f8-49f6-bf24-cc595e5b0b16
-- title:
--   Original intrinsic Gaussian residual limit starts at zero
-- statement:
--   Any original sample-path residual field obtained as the almost-sure all-time limit of the exact original truncated Gaussian residuals has zero initial value almost surely. The finite cutoff residual vanishes at zero from the original X-zero field and the already Proved small/large source jump zero-time identities. This is the initialisation needed for its centred original-filtration martingale law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, R 0 ω = 0 := by sorry
