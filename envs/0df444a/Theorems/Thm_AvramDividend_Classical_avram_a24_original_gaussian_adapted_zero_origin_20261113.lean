-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_adapted_zero_origin_20261113
-- name    : AvramDividend.Classical.avram_a24_original_gaussian_adapted_zero_origin_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:47:05.44761+00:00
-- url     : https://prove2.me/theorems/f8000f9d-9d80-4781-bacd-c9861154eecd
-- title:
--   Original physical Gaussian limit admits globally raw-filtration adapted zero-at-origin representative
-- statement:
--   On the exact original filtered probability space, the physical Gaussian intrinsic residual has a globally measurable adapted source representative starting at zero for every sample path and agreeing with the physical limit at every time almost surely.
-- source:
--   A24 canonical global raw F_t adaptation and Proved 4f4d81f6 original Gaussian source zero-time identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin18_original_intrinsic_gaussian_residual_zero_time_public
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original Gaussian source has a globally raw-filtration adapted representative starting exactly at zero. -/

theorem AvramDividend.Classical.avram_a24_original_gaussian_adapted_zero_origin_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) := by sorry
