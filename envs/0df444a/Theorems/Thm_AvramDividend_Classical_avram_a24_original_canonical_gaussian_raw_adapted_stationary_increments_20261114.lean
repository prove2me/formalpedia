-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_raw_adapted_stationary_increments_20261114
-- name    : AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_stationary_increments_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:05:49.16231+00:00
-- url     : https://prove2.me/theorems/8c27947a-d4a8-4bdb-81e0-f4ebabef0027
-- title:
--   Globally adapted canonical original Gaussian residual has exactly stationary increment laws
-- statement:
--   The original canonical Gaussian residual source, globally adapted to its raw filtration and exactly zero at origin, has stationary pushforward laws of increments over every deterministic interval length.
-- source:
--   A24 canonical zero-origin globally adapted source and Proved 5130dad2 original physical Gaussian limit stationary-increment law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The globally source-adapted Gaussian residual has a stationary-increment law at every deterministic start. -/

theorem AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_stationary_increments_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) ∧
      (∀ T : ℝ≥0, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) := by sorry
