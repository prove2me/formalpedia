-- Prove2me | Theorems.Thm_FlatlyFoliated_identity_82_83
-- name    : FlatlyFoliated.identity_82_83
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:42:33.719816+00:00
-- url     : https://prove2.me/theorems/293504d5-2900-455c-830a-3e716278afc5
-- title:
--   Identity (82)–(83) — divergence form of $(\Delta f)^2-\|f_{ij}\|^2-2\Lambda$
-- statement:
--   For every smooth $f:\mathbb R^3\to\mathbb R$ and every $\Lambda\in\mathbb R$,
--   $$\nabla\cdot\Big(\Delta f\,\nabla f-\operatorname{Hess}f(\nabla f,\cdot)-\tfrac{\Lambda}{3}\cdot2r\partial_r\Big)=(\Delta f)^2-\|f_{ij}\|^2-2\Lambda,$$
--   where $r\partial_r$ is the position vector field $x$. In coordinates the vector field has components $\Delta f\,f_j-\sum_i f_{ij}f_i-\tfrac{2\Lambda}{3}x_j$.
--
--   This identity drives the divergence-theorem argument in the proof of Theorem 5.
-- source:
--   Bray, Hamm, Hirsch, Wheeler, Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, https://arxiv.org/abs/1911.00967, p. 17, equations (82)–(83)

import Mathlib
import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff

namespace FlatlyFoliated

/-- Identity (82)–(83):
`∇·(Δf ∇f − Hess f(∇f,·) − (Λ/3)·2r∂ᵣ) = (Δf)² − ‖fᵢⱼ‖² − 2Λ`. -/
theorem identity_82_83 (Λ : ℝ) (f : R3 → ℝ) (hf : ContDiff ℝ ∞ f) (x : R3) :
    ∑ j, pd j (fun y => lap f y * pd j f y - ∑ i, pd j (pd i f) y * pd i f y
        - (2 * Λ / 3) * y j) x =
      lap f x ^ 2 - hessNormSq f x - 2 * Λ := by sorry

end FlatlyFoliated
