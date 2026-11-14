-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_raw_adapted_independent_increments_20261113
-- name    : AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_independent_increments_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:02:16.459406+00:00
-- url     : https://prove2.me/theorems/c792676b-c7c6-4374-8ec3-a657f13cdb5e
-- title:
--   Canonical original Gaussian residual is globally adapted with independent increments relative to the raw source filtration
-- statement:
--   One globally raw-filtration adapted zero-origin source process agreeing almost surely at all horizons with the intrinsic Gaussian residual has independent increments relative to the original past sigma-algebras, without assuming their completion.
-- source:
--   A24 globally adapted canonical zero-origin source, A24 coherent future-past independent increments, and AE independence preservation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- One canonical original-filtration adapted Gaussian residual source has genuinely independent increments. -/

theorem AvramDividend.Classical.avram_a24_original_canonical_gaussian_raw_adapted_independent_increments_20261113
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
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) := by sorry
