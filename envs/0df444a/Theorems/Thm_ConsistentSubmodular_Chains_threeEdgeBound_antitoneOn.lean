-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_threeEdgeBound_antitoneOn
-- name    : ConsistentSubmodular.Chains.threeEdgeBound_antitoneOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:07.035108+00:00
-- url     : https://prove2.me/theorems/1f9b50af-2b57-48b5-ba8f-56545a56e238
-- title:
--   The three-edge bound $F$ is nonincreasing on $[L,\infty)$
-- statement:
--   Let $q=q^\star$, let $L=\frac1{1-q}$, and let
--   $$F(y)=3+3q-qy-2\sqrt{qy}-2\sqrt{q+1/y}.$$
--   Then $F$ is nonincreasing on $[L,\infty)$: for $L\le y\le y'$ one has $F(y')\le F(y)$.
--
--   The paper's argument is that on this range $F'(y)<0$. This monotonicity reduces the case of a middle vertex $y\ge L$ in a three-edge chain to the endpoint $y=L$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L373-L431 (`ConsistentSubmodular.Chains.threeEdgeBound_antitoneOn`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.threeEdgeBound_antitoneOn : AntitoneOn threeEdgeBound (Set.Ici collapseBound) := by sorry
