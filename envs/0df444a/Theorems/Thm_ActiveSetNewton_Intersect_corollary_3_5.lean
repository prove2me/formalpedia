-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_corollary_3_5
-- name    : ActiveSetNewton.Intersect.corollary_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:08.243086+00:00
-- url     : https://prove2.me/theorems/e0920c15-88b0-49b8-92b5-19822fdf7b75
-- title:
--   Corollary 3.5, p. 6 — for every Lipschitz R : Y ∩ W → X fixing z, the iteration x ← R(y(x)) converges quadratically to z
-- statement:
--   **Corollary 3.5 (Semi-linearization for intersecting manifolds).** In the setting of Theorem 3.1 — $z$ an isolated, transversal point of intersection of two $C^{(2)}$-manifolds $\mathcal X$ and $\mathcal Y$ around $z$ in a Euclidean space $\mathbf E$ — there is an open neighborhood $W$ of $z$ on which the semi-linearization point $y(x)$, the unique point of $(x+T_{\mathcal X}(x))\cap\mathcal Y\cap W$, is defined for every $x\in\mathcal X\cap W$, and with the following property. For every map $R$ that is Lipschitz on $\mathcal Y\cap W$, maps $\mathcal Y\cap W$ into $\mathcal X$, and satisfies $R(z)=z$, starting from any point $x\in\mathcal X$ near $z$ the iteration
--   $$x\;\leftarrow\;R\big(y(x)\big)$$
--   converges quadratically to $z$.
--
--   This is the basic Newton scheme for the intersection problem $\mathcal X\cap\mathcal Y=\{z\}$: linearize $\mathcal X$, intersect with $\mathcal Y$, and restore the result to $\mathcal X$ by any Lipschitz map fixing $z$.
--
--   **Formalization Note** The paper takes $R:\mathcal Y\to\mathcal X$ Lipschitz on all of $\mathcal Y$. Here $R$ need only be Lipschitz on $\mathcal Y\cap W$ and map $\mathcal Y\cap W$ into $\mathcal X$, which is a weaker hypothesis and hence a stronger statement; it is the form Theorem 5.1 uses, with $R=Q\circ S$ defined only on $\mathcal Y\cap W$. "Converges quadratically" is the predicate of the definitions file: one constant $C$ for all starting points within some $\delta$ of $z$, iterates staying in $\mathcal X$ within $\delta$ of $z$, the bound $|x_{n+1}-z|\le C|x_n-z|^2$, and convergence to $z$.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, p. 6, Corollary 3.5

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

/-- Corollary 3.5 (Semi-linearization for intersecting manifolds), p. 6: for every map `R` that
is Lipschitz on `Y ∩ W`, maps `Y ∩ W` into `X` and fixes `z`, the iteration `x ← R(y(x))`
converges quadratically to `z`. -/
theorem corollary_3_5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {X Y : Set E} {z : E}
    (hX : IsCManifoldAround 2 X z) (hY : IsCManifoldAround 2 Y z)
    (hiso : IsolatedIntersection X Y z) (htr : TransversalAt X Y z) :
    ∃ W : Set E, IsOpen W ∧ z ∈ W ∧ ∃ y : E → E,
      (∀ x ∈ X ∩ W, (y x ∈ linApprox X x ∧ y x ∈ Y ∩ W) ∧
        ∀ y' : E, y' ∈ linApprox X x → y' ∈ Y ∩ W → y' = y x) ∧
      ∀ R : E → E, Set.MapsTo R (Y ∩ W) X → (∃ K, LipschitzOnWith K R (Y ∩ W)) → R z = z →
        ConvergesQuadratically (fun x => R (y x)) X z := by sorry

end ActiveSetNewton.Intersect
