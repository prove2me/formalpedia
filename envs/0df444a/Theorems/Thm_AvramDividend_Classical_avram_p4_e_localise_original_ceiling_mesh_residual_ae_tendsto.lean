-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ceiling_mesh_residual_ae_tendsto
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ceiling_mesh_residual_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:36:53.635148+00:00
-- url     : https://prove2.me/theorems/62099987-6f6a-49c7-9833-7fdc151335b5
-- title:
--   Original bounded ceiling mesh yields almost-sure residual stopped-value convergence
-- statement:
--   For the actual original ruin-clipped source clock, a nonnegative vanishing grid-mesh envelope and a.s. right-continuous original residual process yield almost-sure convergence of sampled residual values at the first grid ceiling to the exact τ-stopped residual. This combines the source-specific pathwise squeeze with a.e. right-continuity and supplies the hAs premise needed in the bounded true-martingale L1/L2 mean-limit lemmas, without falsely inferring an L1 bound or true martingale from local properties.
-- source:
--   New P4-E original source clock squeeze theorem be6ac215 and right-continuous sampled residual path theorem d520d51b; both must be Proved before proof submission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_residual_ceiling_values_ae_tendsto

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ceiling-grid mesh bounds and right-continuous residual paths yield stopped-value a.s. convergence. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ceiling_mesh_residual_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hBounds : ∀ k ω, τ ω ≤ e k (K k ω) ∧
      e k (K k ω) ≤ τ ω + δ k)
    (f : ℝ≥0 → Ω → ℝ)
    (hRight : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω)
      (Set.Ici (τ ω)) (τ ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => f (e k (K k ω)) ω)
      atTop (𝓝 (f (τ ω) ω)) := by sorry
