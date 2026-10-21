-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_theorem_5_1_a
-- name    : ActiveSetNewton.Intersect.theorem_5_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:00.5714+00:00
-- url     : https://prove2.me/theorems/451bbc07-9ea9-42a4-bde7-84d90456c157
-- title:
--   Theorem 5.1(a), p. 9 — for every small ball W around z, the image M = P(X ∩ W) is a C(2)-manifold around z
-- statement:
--   Let $\mathbf E$ be a Euclidean space and let $z$ be an isolated, transversal point of intersection of two $C^{(2)}$-manifolds $\mathcal X$ and $\mathcal Y$ around $z$. Let $P$ map $\mathcal X$ into $\mathcal Y$, fix $z$ ($P(z)=z$), and be $C^{(2)}$-smooth and constant rank nearby $z$ on $\mathcal X$. Then there is $r>0$ such that for every $0<\varepsilon\le r$, writing $W=B(z,\varepsilon)$ for the open ball,
--   $$\mathcal M = P(\mathcal X\cap W)\ \text{ is a } C^{(2)}\text{-manifold around } z .$$
--
--   This is part (a) of Theorem 5.1: the constant-rank map $P$ carves out of $\mathcal Y$ an "active" submanifold $\mathcal M$ through $z$, onto which the active-set method projects.
--
--   **Formalization Note** "For any sufficiently small neighborhood $W$ of $z$" ranges over open balls $B(z,\varepsilon)$, $0<\varepsilon\le r$. "$C^{(2)}$-smooth and constant rank nearby" means $C^{(2)}$ on an open set of $\mathbf E$ around $z$, with the rank of $DP(x)$ on $T_{\mathcal X}(x)$ constant for $x\in\mathcal X$ near $z$ (see the definitions file).
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, p. 9, Theorem 5.1(a)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

open Metric

/-- Theorem 5.1(a), p. 9: for every sufficiently small ball `W = B(z, ε)`, the image
`M = P(X ∩ W)` is a `C^(2)`-manifold around `z`. -/
theorem theorem_5_1_a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E} {P : E → E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z)
    (hPXY : Set.MapsTo P X Y) (hPz : P z = z) (hP : HasConstantRankNear P X z) :
    ∃ r > 0, ∀ ε, 0 < ε → ε ≤ r → IsCManifoldAround 2 (P '' (X ∩ ball z ε)) z := by sorry

end ActiveSetNewton.Intersect
