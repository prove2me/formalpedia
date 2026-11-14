-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
-- name    : AvramDividend.Classical.avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T21:02:26.482162+00:00
-- url     : https://prove2.me/theorems/dc168d3d-d08e-42b1-96a4-baed4c034f7f
-- title:
--   Original localised Gaussian fixed-level occupation admits an explicit inverse-mesh bound (correct Real.toNNReal declaration)
-- statement:
--   For the original unbounded-variation zero-jump Levy process, genuine adapted monotone dividend strategy, finite physical horizon n and terminal dividend-variation localisation M, the probability-by-time mass of reserve hits at a prescribed spatial level is bounded for every positive integer mesh refinement m by the explicit finite Gaussian constant (1+M+2 n/(sigma sqrt(2 pi)))/m. This sharp quantitative grid estimate follows by combining the original source Gaussian small-ball probability on good cells, the monotone dividend variation bad-cell count, time Fubini and the inverse-square-root kernel integral. It strengthens and directly implies existing B274, which only asks for some positive finite constant. The public statement uses pinned Lean Real.toNNReal for the nonnegative constant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB276b_original_gaussian_localized_explicit_mesh_mass_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n M : ℕ) (m : ℕ) (hm : 0 < m) :
    (P.prod volume)
      {z : Ω × ℝ |
        0 < z.2 ∧ z.2 < (n : ℝ) ∧
        x + X.X (Real.toNNReal z.2) z.1 -
          rightLimit D (Real.toNNReal z.2) z.1 = b ∧
        D n z.1 - D 0 z.1 ≤ (M : ℝ)} ≤
      (Real.toNNReal
        (1 + (M : ℝ) +
          (2 * (n : ℝ)) /
            (X.σ * Real.sqrt (2 * Real.pi))) : ℝ≥0∞) *
            (m : ℝ≥0∞)⁻¹ := by sorry
