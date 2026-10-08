-- Prove2me | Theorems.Thm_ConvexOptAlg_MirrorProx_lemma_4_1
-- name    : ConvexOptAlg.MirrorProx.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:22:51.113356+00:00
-- url     : https://prove2.me/theorems/c925566d-f253-4021-ac24-08c975720fbb
-- title:
--   Lemma 4.1, pp. 298–299 — (∇Φ(Π^Φ_X(y)) − ∇Φ(y))⊤(Π^Φ_X(y) − x) ≤ 0 and D_Φ(x, Π^Φ_X(y)) + D_Φ(Π^Φ_X(y), y) ≤ D_Φ(x, y)
-- statement:
--   Let $\|\cdot\|$ be a norm on a finite-dimensional real space, $\mathcal X$ a compact convex set, $\mathcal D$ a convex open set with $\mathcal X\subseteq\overline{\mathcal D}$ and $\mathcal X\cap\mathcal D\neq\emptyset$, and $\Phi$ a mirror map on $\mathcal D$ with Bregman divergence $D_\Phi$. Let $x\in\mathcal X\cap\mathcal D$ and $y\in\mathcal D$, and let $z=\Pi^\Phi_{\mathcal X}(y)$ be a minimizer of $D_\Phi(\cdot,y)$ over $\mathcal X\cap\mathcal D$. Then
--   $$\bigl(\nabla\Phi(z)-\nabla\Phi(y)\bigr)^\top(z-x)\le 0,$$
--   which also implies
--   $$D_\Phi(x,z)+D_\Phi(z,y)\le D_\Phi(x,y).$$
--
--   The lemma says that the Bregman divergence behaves like the squared Euclidean norm with respect to projections (the analogue of Lemma 3.1 for the Euclidean projection). It is used at every projection step of mirror descent and mirror prox.
--
--   **Formalization Note** $\Pi^\Phi_{\mathcal X}(y)$ is given as a point $z$ satisfying the minimizer relation, not as a function. The setting hypotheses (compactness of $\mathcal X$, $\mathcal X\subseteq\overline{\mathcal D}$, $\mathcal X\cap\mathcal D\ne\emptyset$, and the mirror map properties) are the standing assumptions of Chapter 4 and §4.1.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 4.1, pp. 298–299

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

namespace ConvexOptAlg.MirrorProx

/-- Lemma 4.1 (Bubeck, arXiv:1405.4980v2, pp. 298–299). In the setting of Chapter 4 (a norm on a
finite-dimensional space, `X` compact convex) and §4.1 (`D` convex open, `X ⊆ closure D`,
`X ∩ D ≠ ∅`, `Φ` a mirror map on `D`): let `x ∈ X ∩ D`, `y ∈ D`, and let `z = Π^Φ_X(y)` be a
minimizer of `D_Φ(·, y)` over `X ∩ D`. Then
`(∇Φ(z) − ∇Φ(y))⊤(z − x) ≤ 0`, which also implies `D_Φ(x, z) + D_Φ(z, y) ≤ D_Φ(x, y)`. -/
theorem lemma_4_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (x y z : E) (hx : x ∈ X ∩ D) (hy : y ∈ D) (hz : IsBregmanProj X D Φ Φ' y z) :
    (Φ' z - Φ' y) (z - x) ≤ 0 ∧
      bregman Φ Φ' x z + bregman Φ Φ' z y ≤ bregman Φ Φ' x y := by sorry

end ConvexOptAlg.MirrorProx
