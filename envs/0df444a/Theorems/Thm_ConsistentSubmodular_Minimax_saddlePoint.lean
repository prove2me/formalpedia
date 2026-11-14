-- Prove2me | Theorems.Thm_ConsistentSubmodular_Minimax_saddlePoint
-- name    : ConsistentSubmodular.Minimax.saddlePoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:58.937308+00:00
-- url     : https://prove2.me/theorems/64a36755-c583-4c88-a6ab-a41bdb7496d0
-- title:
--   Finite minimax duality as a saddle point
-- statement:
--   Let $w=(w_{i,j})_{0\le i,j\le m}$ be a real square matrix and $\Delta$ the simplex of probability vectors on $\{0,\dots,m\}$. Then there is a value $v\in\mathbb R$ together with
--
--   1. a distribution $a\in\Delta$ such that $\sum_i a_i\,w_{i,j}\ge v$ for every column $j$, and
--   2. a distribution $b\in\Delta$ such that $\sum_j b_j\,w_{i,j}\le v$ for every row $i$.
--
--   This is von Neumann's finite minimax theorem for the matrix $w$, stated through the existence of a saddle point. It is the abstract duality ingredient of Lemma 5 (Appendix A.4).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/Minimax.lean#L149-L167 (`ConsistentSubmodular.Minimax.saddlePoint`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}

theorem ConsistentSubmodular.Minimax.saddlePoint (w : Fin (m + 1) → Fin (m + 1) → ℝ) : ∃ v : ℝ,
    (∃ a : Point m, IsSimplex a ∧ ∀ j, v ≤ ∑ i, a i * w i j) ∧
    (∃ b : Point m, IsSimplex b ∧ ∀ i, ∑ j, b j * w i j ≤ v) := by sorry
