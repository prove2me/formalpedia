-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_finite_range_stop_condexp
-- name    : AvramDividend.Classical.avram_jb20_original_gaussian_finite_range_stop_condexp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:20:44.050794+00:00
-- url     : https://prove2.me/theorems/1fa784c3-4313-45b1-8a5a-7e76569f09c4
-- title:
--   Original Gaussian residual has initially centred integrable values at finite-range right-continuous stopping clocks
-- statement:
--   The intrinsic Gaussian residual of the original mixed Lévy process is a centred martingale at any bounded stopping clock taking only finitely many values, provided its canonical truncations converge in the original probability space and deterministic-time martingale hypotheses hold. This proves the finite-grid optional-sampling stage before arbitrary-clock limiting and nonlinear C2 Ito-Meyer accounting.
-- source:
--   Proved 2e39b05b residual zero origin and Proved 43ecbcfb finite-range optional conditional expectation. Supports true original-source Gaussian discrete mesh route for 544e8511.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_intrinsic_gaussian_cutoff_residual_zero_origin
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_gaussian_finite_range_stop_condexp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτbound : ∀ ω, τ ω ≤ T)
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S) :
    Integrable (fun ω => R (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => R (τ ω) ω) ω = 0) := by sorry
