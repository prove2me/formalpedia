-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_dirSubdiff_nonempty
-- name    : DirKKTBilevel.VP.dirSubdiff_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:48.585962+00:00
-- url     : https://prove2.me/theorems/b4455bb7-1065-4f32-9ad4-45e08eb20903
-- title:
--   Proof of Theorem 4.2(i), p. 20 — a directionally Lipschitz function has a nonempty directional subdifferential
-- statement:
--   Let $\varphi:\mathbb R^n\to[-\infty,+\infty]$ be directionally Lipschitz continuous at $\bar x$ in direction $u$: there are $L,\varepsilon,\delta>0$ such that $\varphi$ is finite on $\bar x+\mathcal V_{\varepsilon,\delta}(u)$ and $|\varphi(x)-\varphi(x')|\le L\|x-x'\|$ for all $x,x'$ there. Then
--   $$\partial\varphi(\bar x;u)\ne\emptyset,$$
--   where $\partial\varphi(\bar x;u)$ is the directional limiting subdifferential of Definition 2.6.
--
--   In the proof of Theorem 5.1 this guarantees an element of $\partial(-V)(\bar x;u)$ even when the multiplier $\lambda_V$ of the value-function constraint vanishes.
--
--   **Formalization Note** The paper states this for the value function $V$ (p. 20, by Rademacher's theorem and [34, Theorem 9.13]); the argument uses only directional Lipschitz continuity, so the statement is made for every such function and applied to $-V$.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 20, proof of Theorem 4.2(i)

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Proof of Theorem 4.2(i), p. 20 (Rademacher's theorem and [34, Theorem 9.13]): an
extended-real function that is directionally Lipschitz continuous at `x` in direction `u` has a
nonempty directional limiting subdifferential `∂φ(x; u)`. -/
theorem dirSubdiff_nonempty {n : ℕ} (φ : E n → EReal) (x u : E n)
    (h : DirLipschitzAtEReal φ x u) : (dirSubdiff φ x u).Nonempty := by sorry

end DirKKTBilevel.VP
