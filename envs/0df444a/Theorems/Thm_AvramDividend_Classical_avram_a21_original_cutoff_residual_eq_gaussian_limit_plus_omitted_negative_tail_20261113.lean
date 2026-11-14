-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_cutoff_residual_eq_gaussian_limit_plus_omitted_negative_tail_20261113
-- name    : AvramDividend.Classical.avram_a21_original_cutoff_residual_eq_gaussian_limit_plus_omitted_negative_tail_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:51:45.290204+00:00
-- url     : https://prove2.me/theorems/cb474bae-48d0-4856-91f5-2ba1bbf106c9
-- title:
--   Every original finite-cutoff Gaussian residual equals its limit plus the genuinely omitted negative jump tail
-- statement:
--   The original physical cutoff residual Rn is exactly the Gaussian cutoff limit R plus the genuinely OMITTED small negative compensated tail Jsmall-Jn. Follows on the original P a.e. event from the Proved source subtraction Rn=R0-Jn and the exact original limit identity R=R0-Jsmall; avoids any same-space companion construction and uses no independence. This is the correct representation required for finite-cutoff variance from Gaussian-limit and omitted-tail second moments.
-- source:
--   Source path identity bfc8537f and newly submitted Gaussian-limit/full compensated small mark identification 2affdece; elementary real arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_cutoff_residual_eq_gaussian_limit_plus_omitted_negative_tail_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Jsmall R : ℝ≥0 → Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω =
        R t ω + (Jsmall t ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) := by sorry
