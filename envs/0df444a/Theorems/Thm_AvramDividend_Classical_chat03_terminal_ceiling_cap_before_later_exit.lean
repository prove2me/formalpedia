-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_terminal_ceiling_cap_before_later_exit
-- name    : AvramDividend.Classical.chat03_terminal_ceiling_cap_before_later_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:36:56.600643+00:00
-- url     : https://prove2.me/theorems/c087df65-1e2e-40cb-96a7-1daaafd69f23
-- title:
--   Ceiling uniform-grid horizon is eventually before any strictly later passage
-- statement:
--   For nonnegative finite times T<τ and a strictly positive uniform-grid mesh tending to zero, the first grid point at or after T lies below τ for all sufficiently fine meshes. Both bounds follow from the accepted ceiling-grid bracket and the positive gap τ−T. This permits finite-horizon grid caps without crossing a later exit.
-- source:
--   Chat03 accepted NNReal uniform-grid ceiling bracket with an elementary topological eventual upper bound; independent of stochastic harmonicity and all unpublished terminal convergence lemmas.

import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

open Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_terminal_ceiling_cap_before_later_exit
    (T τ : ℝ≥0) (hT : T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n) :
    ∀ᶠ n in atTop,
      T ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n ∧
      (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n < τ := by
  sorry
