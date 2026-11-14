-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_collapse_le
-- name    : ConsistentSubmodular.Chains.collapse_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:22.499344+00:00
-- url     : https://prove2.me/theorems/3ac85226-71d3-4924-8e0e-b140edf28a6f
-- title:
--   Inequality (16) — collapsing two consecutive edges
-- statement:
--   Let $q=q^\star=(1-\xi^\star)/\xi^\star$, let $\varphi(x,y)=1-\frac{y}{x}-q\,(x-1)$ be the edge value, and let $L=\frac{1}{1-q}$ be the collapse threshold. For real numbers $x,y,z$ with $1\le z\le y\le x\le L$,
--   $$\varphi(x,y)+\varphi(y,z)\;\le\;\varphi(x,z).$$
--
--   This inequality allows an intermediate vertex $y$ to be deleted from a descending chain without decreasing its value, as long as the chain lies below $L$. It is used to collapse the tail of a chain to a single edge in the numerical core of Lemma 4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/ConsecutiveChains.lean#L264-L285 (`ConsistentSubmodular.Chains.collapse_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.collapse_le {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x)
    (hxL : x ≤ collapseBound) : edgeValue x y + edgeValue y z ≤ edgeValue x z := by sorry
