-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_theorem_3_1
-- name    : ActiveSetNewton.Intersect.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:03.044502+00:00
-- url     : https://prove2.me/theorems/d11b05be-87fc-4f56-929b-92d94ead1c6b
-- title:
--   Theorem 3.1, p. 4 — x + T_X(x) meets Y ∩ W at a unique y(x), and |y(x) − z| = O(|x − z|²)
-- statement:
--   **Theorem 3.1 (Semi-linearization error).** Let $\mathbf E$ be a Euclidean space and let $z$ be an isolated point of intersection of two sets $\mathcal X,\mathcal Y\subset\mathbf E$ that are $C^{(2)}$-manifolds around $z$, intersecting transversally at $z$:
--   $$N_{\mathcal X}(z)\cap N_{\mathcal Y}(z)=\{0\}.$$
--   Then there is an open neighborhood $W$ of $z$ such that, for every $x\in\mathcal X\cap W$, the linear approximation $x+T_{\mathcal X}(x)$ meets $\mathcal Y\cap W$ in exactly one point $y(x)$, and
--   $$|y(x)-z| = O\big(|x-z|^2\big)\qquad\text{as } x\to z,\ x\in\mathcal X .$$
--
--   The point $y(x)$ is a *semi-linearization* step: only $\mathcal X$ is linearized, $\mathcal Y$ is kept as it is. The theorem says this step lands quadratically close to the intersection point, which is the engine of every Newton-type scheme in the paper.
--
--   **Formalization Note** "Isolated point of intersection" means $\mathcal X\cap\mathcal Y\cap V=\{z\}$ for some open $V\ni z$. $y$ is a function on $\mathbf E$ whose values off $\mathcal X\cap W$ are irrelevant; for $x\in\mathcal X\cap W$ the statement asserts both that $y(x)$ lies in $(x+T_{\mathcal X}(x))\cap\mathcal Y\cap W$ and that it is the only such point. The $O$-bound is Mathlib's `IsBigO` along the filter of neighborhoods of $z$ within $\mathcal X$.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, p. 4, Theorem 3.1, equation (3.2)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

open Filter Topology Asymptotics

/-- Theorem 3.1 (Semi-linearization error), p. 4. -/
theorem theorem_3_1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z) :
    ∃ W : Set E, IsOpen W ∧ z ∈ W ∧ ∃ y : E → E,
      (∀ x ∈ X ∩ W, (y x ∈ linApprox X x ∧ y x ∈ Y ∩ W) ∧
        ∀ y' : E, y' ∈ linApprox X x → y' ∈ Y ∩ W → y' = y x) ∧
      (fun x => y x - z) =O[𝓝[X] z] (fun x => ‖x - z‖ ^ 2) := by sorry

end ActiveSetNewton.Intersect
