-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_chainValue_le
-- name    : ConsistentSubmodular.Chains.chainValue_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:32.949193+00:00
-- url     : https://prove2.me/theorems/0fa2f6c0-112e-46af-8954-5dc97607682e
-- title:
--   Chain inequality (14) for chains of arbitrary length
-- statement:
--   Let $q=q^\star$ and $\varphi(x,y)=1-\frac yx-q(x-1)$. For every list $d_0\ge d_1\ge\dots\ge d_N=1$ of reals (all entries at least $1$, last entry exactly $1$),
--   $$\sum_{j<N}\varphi(d_j,d_{j+1})\;\le\;q.$$
--   For a one-element list the sum is empty and equals $0$.
--
--   This is the numerical core of Lemma 4 (Appendix A.6): multiplied by $d_N$, it gives the bound $\Gamma\ge\xi^\star$ on the adaptivity gap of nonincreasing consecutive intervals with the equalizing distribution. It is obtained by deleting vertices that start a nonpositive edge, collapsing the tail by (16), and bounding three-edge chains by (15) or by the arithmetic–geometric mean bound.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L545-L592 (`ConsistentSubmodular.Chains.chainValue_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.chainValue_le (L : List ℝ) (hL : IsDescendingChain L) : chainValue L ≤ qStar := by sorry
