-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorDescent_lemma_4_1
-- name    : ConvexOptAlg.MirrorDescent.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:03:26.297168+00:00
-- url     : https://prove2.me/theorems/bea8a4ca-8c15-44d3-b450-a2ced80455b1
-- title:
--   Lemma 4.1, pp. 298–299 — the Bregman projection satisfies D_Φ(x, Π(y)) + D_Φ(Π(y), y) ≤ D_Φ(x, y)
-- statement:
--   Let $\mathcal X$ be compact and convex, let $\Phi$ be a mirror map on the convex open set $\mathcal D$ with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\neq\emptyset$, and write $D_\Phi$ for its Bregman divergence. Let $x\in\mathcal X\cap\mathcal D$, $y\in\mathcal D$, and let $\Pi^\Phi_{\mathcal X}(y)$ be a Bregman projection of $y$, i.e. a minimizer of $D_\Phi(\cdot,y)$ over $\mathcal X\cap\mathcal D$. Then
--   $$\big(\nabla\Phi(\Pi^\Phi_{\mathcal X}(y))-\nabla\Phi(y)\big)^\top\big(\Pi^\Phi_{\mathcal X}(y)-x\big)\le0,$$
--   and
--   $$D_\Phi\big(x,\Pi^\Phi_{\mathcal X}(y)\big)+D_\Phi\big(\Pi^\Phi_{\mathcal X}(y),y\big)\le D_\Phi(x,y).$$
--
--   This is the Bregman analogue of the obtuse-angle property of Euclidean projections (Lemma 3.1 of the book); it is what makes the projection step of mirror descent contract Bregman distances to feasible points.
--
--   **Formalization Note** The projection is given as a point $z$ satisfying the minimizing property (a relation, not a function); the book notes it exists and is unique. Linear functionals act by application, so $(\nabla\Phi(z)-\nabla\Phi(y))^\top v$ is `(Φ' z - Φ' y) v`.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 4.1, pp. 298–299 (setting: Ch. 4 preamble, p. 297, and §4.1, p. 298)

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorDescent_Defs

namespace ConvexOptAlg.MirrorDescent

/-- Bubeck, Lemma 4.1, pp. 298–299. In the standing setting of Ch. 4 (`X` compact convex, `Φ` a
mirror map on `D`, `X ⊆ closure D`, `X ∩ D ≠ ∅`), let `x ∈ X ∩ D`, `y ∈ D`, and let `z` be the
Bregman projection `Π^Φ_X(y)`. Then
`(∇Φ(z) − ∇Φ(y))ᵀ(z − x) ≤ 0` and `D_Φ(x, z) + D_Φ(z, y) ≤ D_Φ(x, y)`. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hset : IsMirrorSetting X D Φ Φ')
    (x y z : E) (hx : x ∈ X ∩ D) (hy : y ∈ D)
    (hz : IsBregmanProjection X D Φ Φ' y z) :
    (Φ' z - Φ' y) (z - x) ≤ 0 ∧
      bregman Φ Φ' x z + bregman Φ Φ' z y ≤ bregman Φ Φ' x y := by sorry

end ConvexOptAlg.MirrorDescent
