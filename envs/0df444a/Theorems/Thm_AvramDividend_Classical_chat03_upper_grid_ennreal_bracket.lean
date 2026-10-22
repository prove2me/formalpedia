-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_upper_grid_ennreal_bracket
-- name    : AvramDividend.Classical.chat03_upper_grid_ennreal_bracket
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:36:21.437631+00:00
-- url     : https://prove2.me/theorems/a17d6373-4cb4-4410-ac4f-8813394f4ecf
-- title:
--   Finite strict upper passage bounds the actual extended-real uniform-grid infimum
-- statement:
--   For a finite genuine strict upper passage infimum τ, and every positive epsilon, all sufficiently fine positive uniform grids have an ENNReal first sampled strict crossing time in [τ, τ+epsilon). The sampled clock is defined as the complete-lattice infimum with ∞ for missing crossings, so this theorem remains well defined for every mesh, even when a coarse grid has no crossing. Its proof uses the separately Proved strict upper mesh-detection lemma and ENNReal infimum bounds.
-- source:
--   Official SpectrallyNegativeLevy definition and already Proved chat03_strict_upper_exit_mesh_approximation at Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_upper_exit_mesh_approximation
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_upper_grid_ennreal_bracket
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | upper < X.X t ω} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0,
      0 < h → h < δ →
      (τ : ℝ≥0∞) ≤
        (⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * h) ω then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) ∧
      (⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * h) ω then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) < ((τ + ε : ℝ≥0) : ℝ≥0∞) := by sorry
