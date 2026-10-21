-- Prove2me | Theorems.Thm_ActiveSetNewton_Intersect_tangentSpace_eq_ker
-- name    : ActiveSetNewton.Intersect.tangentSpace_eq_ker
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:04.868199+00:00
-- url     : https://prove2.me/theorems/32193477-8cca-40a1-858c-2bd44022c891
-- title:
--   §2, p. 4 — T_X(z) = Null DF(z) = Range DG(0) and N_X(z) = Range DF(z)* = Null DG(0)*, for every defining map F and coordinate system G
-- statement:
--   Let $\mathbf E$ be a Euclidean space, $r\ge 1$, and let $\mathcal X\subset\mathbf E$ contain $z$. Suppose $F:\mathbf E\to\mathbf R^m$ is $C^{(r)}$-smooth with surjective derivative $DF(z)$ and $\mathcal X\cap V=F^{-1}(0)\cap V$ for an open set $V\ni z$, so that $\mathcal X$ is a $C^{(r)}$-manifold around $z$. Then the tangent cone of $\mathcal X$ at $z$ is already the linear subspace $\mathrm{Null}\,DF(z)$, and
--   $$T_{\mathcal X}(z)=\mathrm{Null}\big(DF(z)\big),\qquad N_{\mathcal X}(z)=\mathrm{Range}\big(DF(z)^*\big).$$
--   Moreover, for every local coordinate system — an open set $U\ni 0$ of $\mathbf R^k$ and a map $G$ that is $C^{(r)}$-smooth on $U$, with $G(0)=z$, injective derivative $DG(u)$ at every $u\in U$, $G(U)\subset\mathcal X$, and $G(U)\supset\mathcal X\cap V'$ for some open $V'\ni z$ —
--   $$T_{\mathcal X}(z)=\mathrm{Range}\big(DG(0)\big),\qquad N_{\mathcal X}(z)=\mathrm{Null}\big(DG(0)^*\big).$$
--   Here $T_{\mathcal X}(z)$ is the span of the tangent cone, $N_{\mathcal X}(z)$ its orthogonal complement, and $^*$ denotes the adjoint.
--
--   In particular these two orthogonal complements do not depend on the choice of $F$ or $G$, which is what makes transversality ($N_{\mathcal X}(z)\cap N_{\mathcal Y}(z)=\{0\}$) a well-defined condition, and it identifies the intrinsic tangent space used throughout the mission with the classical one.
--
--   **Formalization Note** The page's display writes $T_{\mathcal X}(x)$ and $N_{\mathcal X}(x)$ on the left, where $z$ is meant; the statement is at $z$. It quantifies over every $F$ and every $G$ with the defining properties, not over a chosen pair. "Range $G(U)$ a neighborhood of $z$ in $\mathcal X$" is read as $G(U)\subset\mathcal X$ and $G(U)$ containing $\mathcal X\cap V'$ for an open $V'\ni z$. $\mathbf R^m$ and $\mathbf R^k$ are `EuclideanSpace ℝ (Fin m)` and `EuclideanSpace ℝ (Fin k)`, so the adjoints are the Hilbert-space adjoints.
-- source:
--   Lewis & Wylie, Active-set Newton methods and partial smoothness, arXiv:1902.00724v1, pp. 3–4, §2, definition of a C(r)-manifold (p. 3) and the display of the tangent and normal spaces (p. 4)

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSetNewton_Intersect_Basic

namespace ActiveSetNewton.Intersect

/-- §2, p. 4 (display): for a `C^(r)`-manifold `X` around `z` (`r ≥ 1`) and any defining map `F`
(and any local coordinate system `G`), `T_X(z) = Null(DF(z)) = Range(DG(0))` and
`N_X(z) = Range(DF(z)^*) = Null(DG(0)^*)`; the tangent cone itself is `Null(DF(z))`. -/
theorem tangentSpace_eq_ker {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℕ} (hr : 1 ≤ r) {X : Set E} {z : E} (hz : z ∈ X)
    {m : ℕ} {F : E → EuclideanSpace ℝ (Fin m)} (hF : ContDiff ℝ r F)
    (hDF : Function.Surjective (fderiv ℝ F z))
    {V : Set E} (hV : IsOpen V) (hzV : z ∈ V) (hXV : X ∩ V = F ⁻¹' {0} ∩ V) :
    tangentConeAt ℝ X z = (LinearMap.ker (fderiv ℝ F z : E →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : Set E) ∧
    ProjLikeRetr.Retractor.tangentSpace X z =
      LinearMap.ker (fderiv ℝ F z : E →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
    ProjLikeRetr.Retractor.normalSpace X z =
      LinearMap.range
        (ContinuousLinearMap.adjoint (fderiv ℝ F z) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] E) ∧
    ∀ (k : ℕ) (U : Set (EuclideanSpace ℝ (Fin k))) (G : EuclideanSpace ℝ (Fin k) → E),
      IsOpen U → 0 ∈ U → ContDiffOn ℝ r G U → G 0 = z →
      (∀ u ∈ U, Function.Injective (fderiv ℝ G u)) →
      G '' U ⊆ X → (∃ V' : Set E, IsOpen V' ∧ z ∈ V' ∧ X ∩ V' ⊆ G '' U) →
      ProjLikeRetr.Retractor.tangentSpace X z =
        LinearMap.range (fderiv ℝ G 0 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) ∧
      ProjLikeRetr.Retractor.normalSpace X z =
        LinearMap.ker
          (ContinuousLinearMap.adjoint (fderiv ℝ G 0) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by sorry

end ActiveSetNewton.Intersect
