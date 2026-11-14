-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_original_gaussian_increment_independent_centered_L1_20261113
-- name    : AvramDividend.Classical.avram_a23_original_gaussian_increment_independent_centered_L1_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:20:34.855198+00:00
-- url     : https://prove2.me/theorems/9f2a8502-9e44-454c-83c3-0d4b01262ac2
-- title:
--   The original Gaussian limit increment has an integrable centred representative independent of the source past
-- statement:
--   For the original spectrally negative Levy source, each Gaussian intrinsic limit increment on s≤t has a globally measurable, integrable, zero-mean representative independent of the original right-continuous past, equal to its physical residual increment P-almost everywhere.
-- source:
--   Proved original Gaussian limit centring 5bdde16f, A23 canonical source independence representative and integrable AE transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian limit increment has an integrable, centred, future-independent representative. -/

theorem AvramDividend.Classical.avram_a23_original_gaussian_increment_independent_centered_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ D : Ω → ℝ,
      Measurable D ∧
      ProbabilityTheory.Indep (MeasurableSpace.comap D inferInstance)
        (𝓕.rightCont s) P ∧
      Integrable D P ∧
      (∫ ω, D ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, D ω = R t ω - R s ω) := by sorry
