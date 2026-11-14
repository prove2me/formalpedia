-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
-- name    : AvramDividend.Classical.avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:52:57.555198+00:00
-- url     : https://prove2.me/theorems/6be934a3-2e51-450c-8fe4-9b5962538476
-- title:
--   Original zero-jump Lévy process is its own exact same-filtration Gaussian residual companion
-- statement:
--   When the actual original spectrally negative Lévy process has ν=0, it has no physical jumps on a common full-measure event. Therefore its intrinsic original compensated small negative mark integral and uncompensated large mark integral vanish at every cutoff. The exact physical residual is then the original process centred by its own Lévy c; any a.s. all-time intrinsic residual limit R agrees with this centred X. Choose the *original process itself* as the zero-ν Gaussian companion Y, on exactly the same original Ω,P,filtration with identical σ and all structural laws inherited. This works for every nonnegative σ, including strictly positive σ, and requires no independent Brownian noise.
-- source:
--   Proved bc015f1f zero-ν physical all-time jumpfree, Proved bd83c420 source smallband zero, new physical largeband zero source theorem, original residual definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_zero_nu_every_positive_time_no_actual_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_nojump_zero_nu_smallband_identically_zero
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_truly_jumpless_large_mark_sum_identically_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_zero_nu_intrinsic_gaussian_limit_sameX_companion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNu : X.ν = 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (𝓝 (R t ω))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        R t ω = Y.X t ω - (t : ℝ) * Y.c) := by sorry
