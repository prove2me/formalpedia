-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_theorem3_chain
-- name    : ConsistentSubmodular.GridStream.theorem3_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:10.108998+00:00
-- url     : https://prove2.me/theorems/32ea6566-111f-4c68-93c7-e5d0f11762c0
-- title:
--   Theorem 3 — the chain of inequalities for the coverage bound
-- statement:
--   Let $k,x,j,\varepsilon$ be real numbers with $k>0$, $j\ge1$, $0<\varepsilon<\tfrac14$, $\varepsilon k\ge1$, and
--   $$\tfrac k2\le x\le \tfrac k2+\varepsilon k .$$
--   Then
--   $$x\,k+(k-x)(k+j)-x\,(k-x)\;\le\;\Bigl(\tfrac34+6\varepsilon\Bigr)\,k\,(k+j-1).$$
--
--   The left-hand side is the coverage bound for a set holding $x$ rows. The proof in Appendix B.1 passes through the bound $\tfrac34(k+2\varepsilon k)^2+\tfrac{kj}{2}$ and then $\tfrac34(1+2\varepsilon)^2(1+\varepsilon)\,k\,(k+j-1)\le(\tfrac34+6\varepsilon)\,k\,(k+j-1)$. This is the final arithmetic step of the argument for Theorem 3.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStream.lean#L124-L153 (`ConsistentSubmodular.GridStream.theorem3_chain`)

import Mathlib

open scoped BigOperators
open Finset

theorem ConsistentSubmodular.GridStream.theorem3_chain {k x j ε : ℝ} (hk : 0 < k) (hx0 : k / 2 ≤ x) (hx1 : x ≤ k / 2 + ε * k)
    (hj : 1 ≤ j) (hε0 : 0 < ε) (hε4 : ε < 1 / 4) (hεk : 1 ≤ ε * k) :
    x * k + (k - x) * (k + j) - x * (k - x) ≤ (3 / 4 + 6 * ε) * (k * (k + j - 1)) := by sorry
