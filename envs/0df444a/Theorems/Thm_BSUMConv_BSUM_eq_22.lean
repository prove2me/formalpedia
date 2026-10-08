-- Prove2me | Theorems.Thm_BSUMConv_BSUM_eq_22
-- name    : BSUMConv.BSUM.eq_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:52.967984+00:00
-- url     : https://prove2.me/theorems/4450c626-fb67-4a08-a08f-bb1130253919
-- title:
--   (22), p. 12 — block minimality of z gives u′_k(x_k, z; d_k)|_{x_k=z_k} ≥ 0 for feasible d_k
-- statement:
--   Let $\mathcal X=\mathcal X_1\times\cdots\times\mathcal X_n$ with each $\mathcal X_i$ convex, let $u_k(x_k,y)$ be real functions, and let $z\in\mathcal X$ satisfy $u_k(z_k,z)\le u_k(x_k,z)$ for all $x_k\in\mathcal X_k$ and every block $k$. Then
--
--   $$u_k'(x_k,z;d_k)\Big|_{x_k=z_k}\ \ge\ 0\qquad\forall\,d_k\in\mathbb R^{m_k}\ \text{with}\ d_k+z_k\in\mathcal X_k,\quad k=1,\dots,n,$$
--
--   where $u_k'(x_k,z;d_k)=\liminf_{\lambda\downarrow0}\,(u_k(x_k+\lambda d_k,z)-u_k(x_k,z))/\lambda$ is the directional derivative in the variable $x_k$ only.
--
--   Combined with (B3), this turns block minimality of the surrogate into coordinatewise stationarity of $f$.
--
--   **Formalization Note** The directional derivative is extended-real valued (a liminf), as in the referenced setting.
-- source:
--   Razaviyayn, Hong & Luo, arXiv:1209.2385v1, p. 12, proof of Theorem 2(a), display (22)

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting

namespace BSUMConv.BSUM

open TsengBCD.Stationary Filter Topology

/-- (22), p. 12: if `z ∈ X` and `z_k` minimises `u_k(·, z)` over `X_k` for every block `k`,
then `u′_k(x_k, z; d_k)|_{x_k = z_k} ≥ 0` for every `d_k` with `z_k + d_k ∈ X_k`. -/
theorem eq_22 {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (z : X n) (hzX : z ∈ Xset Xs) (hmin : ∀ (k : Fin N), ∀ w ∈ Xs k, u k (z k) z ≤ u k w z) :
    ∀ (k : Fin N) (dk : EuclideanSpace ℝ (Fin (n k))), z k + dk ∈ Xs k →
      0 ≤ dirDeriv (fun xk => (u k xk z : EReal)) (z k) dk := by sorry

end BSUMConv.BSUM
