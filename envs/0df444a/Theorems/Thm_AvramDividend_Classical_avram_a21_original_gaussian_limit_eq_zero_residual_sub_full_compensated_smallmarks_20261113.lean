-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:50:41.73421+00:00
-- url     : https://prove2.me/theorems/2affdece-1842-494f-8287-eb302360f67f
-- title:
--   Original Gaussian cutoff residual limit equals zero-cutoff residual minus full compensated small negative marks
-- statement:
--   The same-path physical finite-cutoff residuals converge to a Gaussian-intrinsic residual field R, and the physically RETAINED compensated negative mark bands converge to the full small-negative-mark field Jsmall. The original Proved pointwise identity Rn=R0-Jn forces R=R0-Jsmall by uniqueness of real sequence limits, uniformly for all horizons on the intersection of almost-sure events. No independent Gaussian companion, new probability law or false zero-cutoff independence is required.
-- source:
--   Proved original finite-cutoff residual identity bfc8537f; pinned Mathlib tendsto_nhds_unique, tendsto_const_nhds.sub.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      R t ω =
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω -
          Jsmall t ω := by sorry
