-- Prove2me | Theorems.Thm_DynTargetMV_existence_uniqueness_QP
-- name    : DynTargetMV.existence_uniqueness_QP
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:40:56.863727+00:00
-- url     : https://prove2.me/theorems/72059d0f-0913-4deb-b6ce-5db945d08ff5
-- title:
--   (2.10), p.10 — the quadratic program has a unique solution $v^*(t)$
-- statement:
--   Under Assumptions 1 and 2, for every $t\in[0,T)$ and every real value of $\psi(t)$, the quadratic program
--   $$
--   \min_{v\in\mathbb R^m}\ \tfrac12v^\top\sigma(t)\sigma(t)^\top v\quad\text{subject to}\quad b(t)^\top v\ge\psi(t),\ Qv\ge0
--   $$
--   has exactly one optimal solution, denoted $v^*(t)$.
--
--   This defines the function $v^*$ on which all three strategies of Theorem 1 are built.
--
--   Differences from the source:
--   - reading: Assumption 1 (ii): I is "the n-dimensional identity matrix" → the m×m identity matrix; reason: σ(t)σ(t)⊤ is m×m, and n is the number of rows of Q
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.10

import Definitions.Def_DynTargetMV_Market_Assumption1
import Definitions.Def_DynTargetMV_Market_Assumption2
import Definitions.Def_DynTargetMV_Market_IsQPSol

open Set

namespace DynTargetMV

/-- Problem (2.10) is feasible and has a unique solution `v*(t)` for every `t ∈ [0,T)`.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, p.10. -/
theorem existence_uniqueness_QP {m d n : ℕ} (M : Market m d n) (hA1 : M.Assumption1)
    (hA2 : M.Assumption2) (ψ : ℝ → ℝ) :
    ∀ t ∈ Ico 0 M.T, ∃! v : Fin m → ℝ, M.IsQPSol ψ t v := by sorry

end DynTargetMV
