-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
-- name    : AvramDividend.Classical.avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:54:18.274753+00:00
-- url     : https://prove2.me/theorems/45dec03a-d041-4c83-9ea1-9b29c63a3429
-- title:
--   Original Gaussian intrinsic cutoff limit is right-continuous at every time simultaneously on one P-conull event
-- statement:
--   The original Gaussian intrinsic residual limit is right-continuous at every time on one source full-measure sample-path event whenever the already established compact-uniform physical cutoff error estimates hold.
-- source:
--   A24 all-path finite-cutoff right continuity, A24 compact to local uniform convergence, A24 one-sided right-continuity preservation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original intrinsic Gaussian limit is right-continuous at every time on one source conull event. -/

theorem AvramDividend.Classical.avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (R : ℝ≥0 → Ω → ℝ)
    (hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => R u ω) (Ici t) t := by sorry
