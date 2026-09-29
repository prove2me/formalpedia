-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/841f9129-89c5-5ff7-9d16-3b3eb6799ca3
-- title:
--   Two-chart Čech cohomology of a line bundle on a finite closed subscheme
-- statement:
--   Let $k$ be a field, let $Z$ and $X$ be schemes, let $x : X \to \operatorname{Spec} k$ and $i : Z \to X$ be morphisms, and assume the composite $i$ followed by $x$, i.e. the structure morphism $Z \to \operatorname{Spec} k$, is finite. Let $N$ be a sheaf of modules on $Z$ which is invertible in the sense that every point of $Z$ has an open neighbourhood $U$ with the pullback of $N$ along $U \hookrightarrow Z$ isomorphic to the unit sheaf of modules on $U$. Let $\mathcal V$ consist of two open subschemes $U_0, U_1 \subseteq X$, each affine, with $U_0 \sqcup U_1 = X$ and $U_0 \cap U_1$ affine. Consider the two-chart Čech datum of the direct image $i_*N$ associated with $\mathcal V$: the $k$-modules $\Gamma(i_*N, U_0)$, $\Gamma(i_*N, U_1)$, $\Gamma(i_*N, U_0 \cap U_1)$ (the $k$-structure coming from $x$) with the two restriction maps $r_0, r_1$, and its differential $(m_0,m_1) \mapsto r_1 m_1 - r_0 m_0$. Then its $H^0$, the kernel of that differential, is a finite $k$-module; its $H^1$, the quotient of $\Gamma(i_*N, U_0 \cap U_1)$ by the image of that differential, is subsingleton; and for every point $t$ of $\operatorname{Spec} k$ one has $\dim_k H^0 =$ `(i ≫ x).finrank t`, the rank of the finite morphism $Z \to \operatorname{Spec} k$ at $t$.
--
--   This is the two-chart Čech computation of the cohomology of an invertible sheaf supported on a finite scheme over a field: $H^1$ vanishes and $h^0$ equals the degree of $Z \to \operatorname{Spec} k$. It feeds the Euler-characteristic computations for sheaves on curves obtained by gluing two affine pieces, and for invertible ideal-sheaf data twisted by such a module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finite_H0_and_subsingleton_H1_sectionsOf_pushforward_of_isFinite
    {k : Type u} [Field k] {Z X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (i : Z ⟶ X) (hZ : IsFinite (i ≫ x))
    (N : Z.Modules) (hN : Scheme.Modules.IsInvertible N) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite k (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H0 ∧
      Subsingleton (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H1 ∧
      ∀ t : Spec (CommRingCat.of k),
        Module.finrank k (𝒱.sectionsOf x ((Scheme.Modules.pushforward i).obj N)).H0 = (i ≫ x).finrank t := by sorry
