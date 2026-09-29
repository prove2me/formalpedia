-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
-- name    : AlgebraicGeometry.Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/e9467d96-a29e-586b-84b5-ab3cdb6e1301
-- title:
--   V-valued tangent vectors as maps out of the cotangent space
-- statement:
--   Let $K$ be a field, let $X$ be a scheme, let $x \colon X \to \operatorname{Spec} K$ be a morphism and let $pt \colon \operatorname{Spec} K \to X$ satisfy $pt$ followed by $x$ equal to the identity of $\operatorname{Spec} K$, so that $pt$ is a $K$-rational point of $X$ over $x$. Write $p$ for the image under $pt$ of the closed point of $\operatorname{Spec} K$ and equip the stalk $\mathcal O_{X,p}$ with the $K$-algebra structure obtained by composing the inverse of the global-sections isomorphism $\Gamma(\operatorname{Spec} K,\mathcal O) \cong K$, the map on global sections induced by $x$, and the germ map at $p$. The assertion is the existence of a family $\gamma$ assigning, to every type $V$ with an additive commutative group structure and compatible central $K$- and $K^{\mathrm{op}}$-module structures, a bijection between `TangentPoints x pt V` and the $K$-linear maps from `IsLocalRing.CotangentSpace` of $\mathcal O_{X,p}$, the Zariski cotangent space $\mathfrak m_p/\mathfrak m_p^2$, to $V$; here an element of `TangentPoints x pt V` is a morphism $v \colon \operatorname{Spec}(K \oplus V) \to X$ from the spectrum of the trivial square-zero extension such that $v$ followed by $x$ is $\operatorname{Spec}$ of the structure map $K \to K \oplus V$ and such that $\operatorname{Spec}$ of the projection $K \oplus V \to K$ followed by $v$ is $pt$. The family is moreover natural: for all such $V$, $W$, every $K$-linear $\varphi \colon V \to W$ and every $v$ in `TangentPoints x pt V`, the value $\gamma_W$ of the tangent vector obtained by precomposing $v$ with $\operatorname{Spec}$ of $\operatorname{TrivSqZeroExt.map} \varphi$ equals $\gamma_V(v)$ followed by $\varphi$.
--
--   This is the functorial description of the Zariski tangent space at a rational point: tangent vectors with values in a module $V$, i.e. liftings of the point to the spectrum of the trivial square-zero extension $K \oplus V$, are the $K$-linear functionals on $\mathfrak m_p/\mathfrak m_p^2$ with values in $V$, compatibly with linear maps in $V$. It is used to compute cotangent spaces of local rings appearing in curve models and in the work with fake elliptic curves, where tangent vectors are identified with linear-algebra data and dimensions of cotangent spaces are determined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_tangentPoints_equiv_linearMap_cotangentSpace
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (pt : Spec (CommRingCat.of K) ⟶ X) (hpt : pt ≫ x = 𝟙 (Spec (CommRingCat.of K))) :
    letI : Algebra K (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) :=
      ((X.presheaf.germ ⊤ (pt.base (IsLocalRing.closedPoint K)) trivial).hom.comp
        (x.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    ∃ γ : ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V],
        TangentPoints x pt V ≃
          (IsLocalRing.CotangentSpace (X.presheaf.stalk (pt.base (IsLocalRing.closedPoint K))) →ₗ[K] V),
      ∀ (V : Type u) [AddCommGroup V] [Module K V] [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
        (W : Type u) [AddCommGroup W] [Module K W] [Module Kᵐᵒᵖ W] [IsCentralScalar K W]
        (φ : V →ₗ[K] W) (v : TangentPoints x pt V),
        γ W (v.map φ) = φ ∘ₗ γ V v := by sorry
