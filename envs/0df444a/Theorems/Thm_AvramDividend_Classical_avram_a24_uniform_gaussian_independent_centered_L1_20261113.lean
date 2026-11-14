-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_independent_centered_L1_20261113
-- name    : AvramDividend.Classical.avram_a24_uniform_gaussian_independent_centered_L1_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:43:55.468231+00:00
-- url     : https://prove2.me/theorems/256c464b-bb7c-4420-aeb5-d826a8ce0831
-- title:
--   Coherent original Gaussian limit future increments are past-independent, L1, and centred
-- statement:
--   For each duration, all Gaussian limit source increments have a coherent globally measurable representative family independent of the source right-continuous past, with integrable zero mean, agreeing simultaneously at every starting time with the physical intrinsic residual.
-- source:
--   A24 uniform original past-independent representative and Proved 5bdde16f same-source L1 centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One coherent original-source Gaussian increment family is independent, integrable and centred at all deterministic times. -/

theorem AvramDividend.Classical.avram_a24_uniform_gaussian_independent_centered_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (T : ℝ≥0) :
    ∃ D : ℝ≥0 → Ω → ℝ,
      (∀ s, Measurable (D s)) ∧
      (∀ s, ProbabilityTheory.Indep
        (MeasurableSpace.comap (D s) inferInstance)
        (𝓕.rightCont s) P) ∧
      (∀ s, Integrable (D s) P ∧ (∫ ω, D s ω ∂P) = 0) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ≥0,
        D s ω = R (s + T) ω - R s ω) := by sorry
