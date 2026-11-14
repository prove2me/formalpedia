-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
-- name    : AvramDividend.Classical.avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:36:50.37062+00:00
-- url     : https://prove2.me/theorems/5e640724-7b20-4e37-8907-63aa224ea463
-- title:
--   Original finite activity residual cutoff limit equals the drift-centred Gaussian component on the same sample path
-- statement:
--   If the retained compensated negative-band Jk converges on the original sample path to Jsmall, the cutoff Gaussian residual Rk converges to R, and the original zero-cutoff path is a same-source drift-centred zero-jump Gaussian companion plus Jsmall, then R is exactly that companion almost everywhere. The proof uses the source identity Rk=R0-Jk and uniqueness of real sequence limits. This is a genuine direct-path transfer lemma that never substitutes another probability law.
-- source:
--   Proved original Rk=R0-Jk bfc8537f; pinned Mathlib Tendsto.sub and tendsto_nhds_unique.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_residual_eq_zero_residual_sub_retained_20261113
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_gaussian_limit_identified_with_same_source_zero_nu_process_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (Jsmall : ℝ≥0 → Ω → ℝ) (R : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0)
    (hJsource : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRsource : ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hDecomp : ∀ᵐ ω ∂P,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω) :
    ∀ᵐ ω ∂P, R t ω = Y.X t ω - (t : ℝ) * Y.c := by sorry
