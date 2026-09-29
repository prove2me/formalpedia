-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1baseChangeMap_surjective_and_eq_iff_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e1bc2ae9-8fe7-5806-9bdd-49aaa8d4dd49
-- title:
--   Base change of two-chart Čech H¹ along a surjection
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\mathcal V$ a two-affine-open cover datum for $X$: opens $U_0,U_1$ with $U_0$, $U_1$ and $U_0\cap U_1$ affine and $U_0\cup U_1=X$. Let $c\colon X\to\operatorname{Spec}R$ be a morphism, and let $A$ be an $R$-algebra such that $\mathrm{algebraMap}\ R\ A$ is surjective. Associated with $(\mathcal V,c)$ is the two-chart datum with rings $\Gamma(X,U_0)$, $\Gamma(X,U_1)$, $\Gamma(X,U_0\cap U_1)$ and the two restrictions, whose structure-sheaf sections have $H^1$ the quotient of $\Gamma(X,U_0\cap U_1)$ by the range of the Čech differential $(m_0,m_1)\mapsto -r_0m_0+r_1m_1$ on $\Gamma(X,U_0)\times\Gamma(X,U_1)$. Pulling $\mathcal V$ back along the first projection of $X\times_{\operatorname{Spec}R}\operatorname{Spec}A$ gives the corresponding datum over $A$, and $\mathcal V.\mathrm{H1baseChangeMap}\ c\ A$ is the induced map on $H^1$, semilinear over $R\to A$. The assertion is twofold: this map is surjective as a map of sets, and for all classes $x,y$ in $H^1$ its values agree at $x$ and $y$ precisely when $x-y$ lies in $\ker(R\to A)\cdot H^1$, the submodule $\ker(\mathrm{algebraMap}\ R\ A)\bullet\top$.
--
--   This is the right exactness of base change on the top cohomology of a two-term Čech complex, in the concrete form that $\check H^1$ of the structure sheaf on a two-chart cover satisfies $\check H^1(\mathcal V_A,\mathcal O_{X_A})\cong \check H^1(\mathcal V,\mathcal O_X)\otimes_R A=\check H^1(\mathcal V,\mathcal O_X)/I\,\check H^1(\mathcal V,\mathcal O_X)$ for $A=R/I$. It feeds the analysis of fibres of the base-change map on relative Picard data, being used in [`AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre`](thm.html#AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPoints_baseChange_surjective_and_fibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1baseChangeMap_surjective_and_eq_iff_of_surjective
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) := by sorry
