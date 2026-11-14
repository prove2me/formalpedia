-- Prove2me | Theorems.Thm_ConsistentSubmodular_Minimax_guarantee_le_rowMax
-- name    : ConsistentSubmodular.Minimax.guarantee_le_rowMax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:57.446463+00:00
-- url     : https://prove2.me/theorems/72e4c778-7142-4e98-be28-e4ef965131e9
-- title:
--   Weak duality for the payoff matrix
-- statement:
--   Let $w=(w_{i,j})_{0\le i,j\le m}$ be a real matrix and let $a,b$ be probability vectors on $\{0,\dots,m\}$. Then
--   $$\min_j\sum_i a_i\,w_{i,j}\;\le\;\max_i\sum_j b_j\,w_{i,j}.$$
--
--   Indeed the left side is at most $\sum_j b_j\sum_i a_i w_{i,j}=\sum_i a_i\sum_j b_j w_{i,j}$, which is at most the right side. This weak duality gives one direction of Lemma 5 (Appendix A.4): every guarantee is at most every maximal row sum.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/Minimax.lean#L173-L187 (`ConsistentSubmodular.Minimax.guarantee_le_rowMax`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_Minimax

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Minimax
variable {m : ℕ}

theorem ConsistentSubmodular.Minimax.guarantee_le_rowMax (w : Fin (m + 1) → Fin (m + 1) → ℝ) {a b : Point m}
    (ha : IsSimplex a) (hb : IsSimplex b) : guarantee w a ≤ rowMax w b := by sorry
