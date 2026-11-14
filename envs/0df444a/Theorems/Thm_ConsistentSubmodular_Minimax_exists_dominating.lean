-- Prove2me | Theorems.Thm_ConsistentSubmodular_Minimax_exists_dominating
-- name    : ConsistentSubmodular.Minimax.exists_dominating
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:50.265596+00:00
-- url     : https://prove2.me/theorems/d423be5b-496e-4d0b-96f6-72f609d856df
-- title:
--   Separation step of minimax duality
-- statement:
--   Let $w=(w_{i,j})_{0\le i,j\le m}$ be a real $(m+1)\times(m+1)$ matrix, $v\in\mathbb R$, and let $\Delta$ be the simplex of probability vectors on $\{0,\dots,m\}$. Suppose that for every $b\in\Delta$ there is a row $i$ with
--   $$v<\sum_j b_j\,w_{i,j}.$$
--   Then there exists $a\in\Delta$ such that for every column $j$
--   $$v<\sum_i a_i\,w_{i,j}.$$
--
--   This is the separation (theorem of the alternative) step used to prove finite minimax duality, Lemma 5 of Appendix A.4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/Minimax.lean#L70-L147 (`ConsistentSubmodular.Minimax.exists_dominating`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}

theorem ConsistentSubmodular.Minimax.exists_dominating (w : Fin (m + 1) → Fin (m + 1) → ℝ) (v : ℝ)
    (h : ∀ b : Point m, IsSimplex b → ∃ i, v < ∑ j, b j * w i j) :
    ∃ a : Point m, IsSimplex a ∧ ∀ j, v < ∑ i, a i * w i j := by sorry
