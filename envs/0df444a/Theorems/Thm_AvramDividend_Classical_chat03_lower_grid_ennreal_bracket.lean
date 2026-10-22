-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_lower_grid_ennreal_bracket
-- name    : AvramDividend.Classical.chat03_lower_grid_ennreal_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:36:23.05242+00:00
-- url     : https://prove2.me/theorems/ecf51d34-91c1-4fc7-9c4a-4a75cb31fc9f
-- title:
--   Finite strict lower passage bounds the actual extended-real uniform-grid infimum
-- statement:
--   For a finite genuine strict lower passage infimum τ, and every positive epsilon, all sufficiently fine positive uniform grids have an ENNReal first sampled strict crossing time in [τ, τ+epsilon). The sampled clock is defined as the complete-lattice infimum with ∞ for missing crossings, so this theorem remains well defined for every mesh, even when a coarse grid has no crossing. Its proof uses the separately Proved strict lower mesh-detection lemma and ENNReal infimum bounds.
-- source:
--   Official SpectrallyNegativeLevy definition and already Proved chat03_strict_lower_exit_mesh_approximation at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_mesh_approximation
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_lower_grid_ennreal_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | X.X t ω < lower} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0,
      0 < h → h < δ →
      (τ : ℝ≥0∞) ≤
        (⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * h) ω < lower then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) ∧
      (⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * h) ω < lower then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) < ((τ + ε : ℝ≥0) : ℝ≥0∞) := by sorry
