-- Prove2me | Theorems.Thm_BSUMConv_SUM_first_order_at_limit
-- name    : BSUMConv.SUM.first_order_at_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:29.803103+00:00
-- url     : https://prove2.me/theorems/d21baa6f-f115-45c6-affd-6bcf024412a9
-- title:
--   Proof of Theorem 1, p. 8 — if z ∈ 𝒳 minimizes u(·, z) over convex 𝒳 then u′(x, z; d)|_{x=z} ≥ 0 for all d with z + d ∈ 𝒳
-- statement:
--   Let $\mathcal X\subseteq\mathbb R^m$ be convex, $u:\mathbb R^m\times\mathbb R^m\to\mathbb R$, and let $z\in\mathcal X$ satisfy $u(z,z)\le u(x,z)$ for every $x\in\mathcal X$. Then the directional derivative of $x\mapsto u(x,z)$ at $x=z$ is nonnegative in every feasible direction:
--   $$
--   u'(x,z;d)\big|_{x=z}=\liminf_{\lambda\downarrow 0}\frac{u(z+\lambda d,z)-u(z,z)}{\lambda}\ \ge\ 0\qquad\forall\,d\in\mathbb R^m\text{ with }z+d\in\mathcal X .
--   $$
--
--   This is the first-order necessary condition at the limit point of Theorem 1; combined with (A3) it gives $f'(z;d)\ge 0$ for all feasible $d$, i.e. stationarity of $z$.
--
--   **Formalization Note** The directional derivative is the extended-real liminf `TsengBCD.Stationary.dirDeriv` applied to $x\mapsto u(x,z)$.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 8, proof of Theorem 1, the display u′(x, z; d)|_{x=z} ≥ 0, ∀ d ∈ ℝ^m with z + d ∈ 𝒳

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_SUM_Setting

namespace BSUMConv.SUM

open TsengBCD.Stationary

/-- Proof of Theorem 1, p. 8: if `z ∈ 𝒳` minimises `u(·, z)` over the convex set `𝒳`, then
`u′(x, z; d)|_{x=z} ≥ 0` for every `d` with `z + d ∈ 𝒳`. -/
theorem first_order_at_limit {m : ℕ} (Xset : Set (EuclideanSpace ℝ (Fin m)))
    (hconv : Convex ℝ Xset)
    (u : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (hzX : z ∈ Xset) (hmin : ∀ y ∈ Xset, u z z ≤ u y z) :
    ∀ d : EuclideanSpace ℝ (Fin m), z + d ∈ Xset →
      0 ≤ dirDeriv (fun x => (u x z : EReal)) z d := by sorry

end BSUMConv.SUM
