-- Prove2me | Theorems.Thm_ConsistentSubmodular_Minimax_minimax
-- name    : ConsistentSubmodular.Minimax.minimax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:58.150645+00:00
-- url     : https://prove2.me/theorems/b02e9410-2253-43fc-9fa9-ac33d947932a
-- title:
--   Lemma 5 — finite minimax duality for the addition-robustness LP
-- statement:
--   Let $W$ be a window instance (stages $0,\dots,m$, candidates $O_j$ of at most $\kappa$ present elements, arrival prefixes $R_j$, benchmark $P_j=f(O_j\cup R_j)$) with $\kappa\ge 1$ and $f(O_0)>0$. Put $w_{i,j}=f(O_i\cup R_j)/f(O_j\cup R_j)$ and let $\Delta$ be the simplex on $\{0,\dots,m\}$. Let $\rho^\star$ be the value of the linear program (1): the supremum of those $\rho\in[0,1]$ for which some $a\in\Delta$ satisfies $\rho P_j\le\sum_i a_i f(O_i\cup R_j)$ for all $j$. Then
--
--   1. $\rho^\star$ is the greatest element of $\bigl\{\min_j\sum_i a_i w_{i,j}: a\in\Delta\bigr\}$, so $\rho^\star=\max_{a\in\Delta}\min_j\sum_i a_iw_{i,j}$ and the maximum is attained;
--   2. $\rho^\star$ is the least element of $\bigl\{\max_i\sum_j b_j w_{i,j}: b\in\Delta\bigr\}$, so $\rho^\star=\min_{b\in\Delta}\max_i\sum_j b_jw_{i,j}$ and the minimum is attained.
--
--   This is Lemma 5 of Appendix A.4, which is used in the proof of Lemma 2 to produce an $\alpha$-addition-robust distribution from a lower bound on the adaptivity gap.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/Minimax.lean#L216-L263 (`ConsistentSubmodular.Minimax.minimax`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {m : ℕ}
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.Minimax.minimax : MinimaxGoal := by sorry
