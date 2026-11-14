-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
-- name    : AvramDividend.Classical.avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:02:17.26126+00:00
-- url     : https://prove2.me/theorems/b15909f6-8d59-43b2-88d3-2e999d3b7b6a
-- title:
--   Canonical original Gaussian source is globally adapted, exact zero origin, and right-continuous simultaneously almost surely
-- statement:
--   On the exact original uncompleted filtration, one canonical globally adapted Gaussian residual source process vanishes at the origin on every path and is right-continuous at every time simultaneously on one conull event.
-- source:
--   A24 globally raw-adapted zero-origin canonical residual and physical compact-uniform limit right-continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One globally adapted original Gaussian source representative starts at zero and is right-continuous on a common conull event. -/

theorem AvramDividend.Classical.avram_a24_original_gaussian_canonical_adapted_ae_rightcont_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) := by sorry
