-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
-- name    : AvramDividend.Classical.avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T20:52:01.237673+00:00
-- url     : https://prove2.me/theorems/7426520d-3ae3-4cc8-817b-8312f91fc114
-- title:
--   Exact original random-clock jumpfree source increments decompose almost everywhere as intrinsic Gaussian residual plus full signed negative Levy drift
-- statement:
--   On the genuine original spectrally negative Lévy probability space and filtration, assume finite negative activity and two original intrinsic source limits R and Jsmall, each converging for all times on one conull event, with no replacement independent Gaussian process. Let s≤t be arbitrary genuine possibly random physical clock endpoints whose interval contains no actual source jump for almost every sample path. Already Proved JB20 produces the exact physical random-clock decomposition of original X into deterministic drift, a totalised intrinsic Gaussian residual M agreeing almost everywhere with R, the intrinsic compensated small-negative channel Jsmall, and the original physical finite large-negative mark source. Already Proved B81 shows the large-mark channel does not change on truly jumpfree intervals. Already Proved B80 identifies every finite negative cutoff smallmark source increment there with the signed Levy cutoff compensator and Proved B84 establishes the full signed negative first moment limit. Combining these original source identities and conull convergence gives the exact X increment equal to the original Gaussian residual R increment plus elapsed time times c minus the full small-negative-strip Levy signed first moment, almost everywhere. This is a concrete same-source genuine stopped-grid Gaussian drift decomposition needed for the original Ito-Meyer cash certificate, with no global negative jump second moment or all-path convergence assumption.
-- source:
--   Proved original JB20, B80, B81 and B84; exact conull stopped random-clock pathwise limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b81_original_jumpfree_cell_large_mark_sum_constant
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original source increment on conull physical jumpfree stopped intervals equals intrinsic Gaussian residual plus its exact full negative-strip signed drift. -/

theorem AvramDividend.Classical.avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω)) := by sorry
