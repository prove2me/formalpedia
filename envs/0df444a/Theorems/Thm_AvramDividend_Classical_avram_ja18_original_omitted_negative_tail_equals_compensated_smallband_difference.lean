-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
-- name    : AvramDividend.Classical.avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:21:54.058205+00:00
-- url     : https://prove2.me/theorems/8adff42c-98e1-47c3-8afa-6d97aa549473
-- title:
--   Original omitted-negative-tail equals actual smallband compensation error at every finite cutoff
-- statement:
--   An exact original-source pathwise almost-sure identity links the finite-cutoff intrinsic residual error R_n-R to the physical compensated small-negative-mark omission Jsmall-J_n. It relies only on two already-Proved same-source decomposition lemmas and the source cutoff-zero identity. This provides the correct retained-vs-omitted tail bridge for subsequent stochastic-calculus covariance and physical two-noise mesh proofs, with arbitrary finite negative activity and no artificial martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_eq_zero_residual_sub_full_compensated_smallmarks_20261113
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_omitted_negative_tail_equals_compensated_smallband_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω))) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ t : ℝ≥0,
      avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω - R t ω =
        Jsmall t ω - avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω := by sorry
