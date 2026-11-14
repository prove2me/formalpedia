-- Prove2me | Theorems.Thm_ConsistentSubmodular_gridStreamCrossing
-- name    : ConsistentSubmodular.gridStreamCrossing
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:23.575351+00:00
-- url     : https://prove2.me/theorems/033062e0-3516-4895-9e19-2d2fac03c3b7
-- title:
--   Lemma 6 — behavior of $3/4$-approximate trajectories on the grid stream $\Sigma$
-- statement:
--   Let $k\ge1$ and $m\ge0$ be integers. Let $\Sigma$ be the coverage stream of Appendix B.1.1 with $n=k+mk$ sets: first the $k$ row sets $a_1,\dots,a_k$ of the $k\times k$ grid, then for each stage $j=1,\dots,m$ the $k$ column sets $b_{1,j},\dots,b_{k,j}$, where $b_{i,j}$ covers column $i$ of the grid together with the auxiliary elements $u_{i,1},\dots,u_{i,j}$. Let $f$ be the coverage function of this stream, and let $(S_t)_{0\le t\le n}$ be a trajectory with budget $k$ and recourse bound $C$ (any $C$), i.e. $S_0=\emptyset$, $S_t\subseteq X_t$, $|S_t|\le k$, $|S_t\triangle S_{t-1}|\le C$. Assume it is a $3/4$-approximation at every time: $\tfrac34 f(A)\le f(S_t)$ for all $t$ and all $A\subseteq X_t$, $|A|\le k$. Let $n_t$ be the number of row sets in $S_t$. Then:
--
--   1. $n_k\ge 3k/4$ (i.e. $3k\le 4\,n_k$);
--   2. if $m\ge k$, there is a time $t>k$ with $n_t\le k/3$ (i.e. $3n_t\le k$).
--
--   Role: Appendix B.1.2; this crossing forces many rows to be removed during the stages, which drives the impossibility argument of Theorem 3.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/MainResults.lean#L87-L90 (`ConsistentSubmodular.gridStreamCrossing`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open ConsistentSubmodular

theorem ConsistentSubmodular.gridStreamCrossing : GridStreamCrossingGoal := by sorry
