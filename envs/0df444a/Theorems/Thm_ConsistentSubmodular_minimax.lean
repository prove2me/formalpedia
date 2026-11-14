-- Prove2me | Theorems.Thm_ConsistentSubmodular_minimax
-- name    : ConsistentSubmodular.minimax
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:49.332199+00:00
-- url     : https://prove2.me/theorems/bf0f98a6-7e43-4206-8dcb-0b2abb972d52
-- title:
--   Lemma 5 — finite minimax duality for the addition-robustness program
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, core budget $\kappa\ge1$, candidates $O_0,\dots,O_m$ and benchmark $f(O_j\cup R_j)$ at stage $j$, and assume $f(O_0)>0$. Let $w_{i,j}=f(O_i\cup R_j)/f(O_j\cup R_j)$ and let $\rho_\star$ be the value of the linear program (1): the supremum of the $\rho\in[0,1]$ for which some distribution $a$ in the simplex $\Delta$ on $\{0,\dots,m\}$ satisfies $\sum_i a_if(O_i\cup R_j)\ge\rho\,f(O_j\cup R_j)$ for all $j$. Then both of the following hold:
--
--   1. $\rho_\star$ is the greatest element of the set of values $\min_j\sum_i a_iw_{i,j}$ over $a\in\Delta$, so
--   $$\rho_\star=\max_{a\in\Delta}\min_j\sum_i a_iw_{i,j};$$
--   2. $\rho_\star$ is the least element of the set of values $\max_i\sum_j b_jw_{i,j}$ over $b\in\Delta$, so
--   $$\rho_\star=\min_{b\in\Delta}\max_i\sum_j b_jw_{i,j}.$$
--
--   In particular both extrema are attained. This duality is the starting point of the interval-selection formulation in Section 2.3 and Appendix A.4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L49-L51 (`ConsistentSubmodular.minimax`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.minimax : MinimaxGoal := by sorry
