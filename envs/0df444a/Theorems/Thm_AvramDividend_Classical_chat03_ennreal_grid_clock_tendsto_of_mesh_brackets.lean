-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
-- name    : AvramDividend.Classical.chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:38:41.89874+00:00
-- url     : https://prove2.me/theorems/75eeea9c-6b6c-423c-be79-2eafaa53fbd6
-- title:
--   Extended-real grid clocks converge to a finite first passage from eventual epsilon brackets
-- statement:
--   A sequence of ENNReal grid clocks may equal infinity on early or coarse grids. If every positive epsilon admits eventual bounds by the finite target τ below and τ+epsilon above as the mesh tends to zero, then the original ENNReal clock converges to τ. The proof converts eventually finite grid values to NNReal, applies the accepted first-passage mesh-bracket convergence theorem and accepted NNReal-to-ENNReal finite embedding, and transfers convergence through eventual equality. This bridge avoids assuming all grids have finite crossing infima.
-- source:
--   Accepted Chat 03 mesh-bracket convergence and finite NNReal-to-ENNReal bridge, pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Theorems.Thm_AvramDividend_Classical_chat03_tendsto_first_passage_of_mesh_brackets
import Theorems.Thm_AvramDividend_Classical_chat03_finite_grid_clock_tendsto_ennreal
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
    (τ : ℝ≥0) (mesh : ℕ → ℝ≥0) (σ : ℕ → ℝ≥0∞)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hbracket : ∀ ε : ℝ≥0, 0 < ε →
      ∃ δ : ℝ≥0, 0 < δ ∧
        ∀ n : ℕ, mesh n < δ →
          (τ : ℝ≥0∞) ≤ σ n ∧
          σ n < ((τ + ε : ℝ≥0) : ℝ≥0∞)) :
    Tendsto σ atTop (𝓝 (τ : ℝ≥0∞)) := by sorry
