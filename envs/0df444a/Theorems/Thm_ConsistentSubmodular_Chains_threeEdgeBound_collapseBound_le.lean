-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_threeEdgeBound_collapseBound_le
-- name    : ConsistentSubmodular.Chains.threeEdgeBound_collapseBound_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:48.290894+00:00
-- url     : https://prove2.me/theorems/dfcff2f2-9484-42d4-b25d-b8d99a6cb9d0
-- title:
--   The three-edge bound at $L$ is at most $q$
-- statement:
--   Let $q=q^\star$, $L=\frac{1}{1-q}$, and
--   $$F(y)=3+3q-qy-2\sqrt{qy}-2\sqrt{q+1/y}.$$
--   Then
--   $$F(L)\;\le\;q.$$
--
--   Equivalently, with $x^\star=\sqrt{L/q}\ge L$, the sum $\varphi(x^\star,L)+\varphi(L,1)$ equals $F(L)$, since equality holds in both arithmetic–geometric mean inequalities at $(x^\star,L,1)$; this sum is at most $q$ by the two-edge inequality (15). Together with the monotonicity of $F$ on $[L,\infty)$, this gives the bound $q$ for three-edge chains with middle vertex at least $L$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L433-L467 (`ConsistentSubmodular.Chains.threeEdgeBound_collapseBound_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.threeEdgeBound_collapseBound_le : threeEdgeBound collapseBound ≤ qStar := by sorry
