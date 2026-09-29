-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/34095960-1cb7-5bc2-9385-2e3f0ccb7d01
-- title:
--   Integrality of a base change via two base-changed chart rings
-- statement:
--   Let $R$ be a commutative ring and $X$ a scheme equipped with a `TwoAffineOpenCover` $\mathcal V$, that is, two opens $U_0,U_1$ of $X$, both affine open, whose intersection $U_0\sqcap U_1$ is also affine open and which satisfy $U_0\sqcup U_1=\top$. Let $c : X \to \operatorname{Spec} R$ be a morphism; via $c$ the sections rings $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\sqcap U_1)$ become $R$-algebras with restriction maps as $R$-algebra homomorphisms (this is the `Cover` datum `𝒱.cover c`). Let $k$ be a commutative $R$-algebra, and assume that $k\otimes_R A_0$ and $k\otimes_R A_1$ are integral domains and that $k\otimes_R A_{01}$ is nontrivial. Then the fibre product $X\times_{\operatorname{Spec} R}\operatorname{Spec} k$, formed along $c$ and the morphism $\operatorname{Spec}$ of the structure map $R\to k$, is an integral scheme, and the two opens of the pulled-back two-affine cover $\mathcal V$`.pullback` $c$ $k$ — namely the preimages of $U_0$ and of $U_1$ under the first projection — are both nonempty.
--
--   This is the standard criterion for integrality of a base change of a scheme covered by two affine charts: integrality of the two base-changed chart rings plus non-vanishing of the base-changed overlap ring. It is used in the construction of integral models of modular curves, where it is invoked through [`ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero`](thm.html#ModularCurve.isIntegral_pullback_and_nonempty_of_chartMap_of_neZero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.isIntegral_pullback_and_nonempty_of_isDomain_tensorProduct
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (k : Type u) [CommRing k] [Algebra R k]
    [IsDomain (k ⊗[R] (𝒱.cover c).A0)] [IsDomain (k ⊗[R] (𝒱.cover c).A1)]
    [Nontrivial (k ⊗[R] (𝒱.cover c).A01)] :
    IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R k)) ∧
      Nonempty (𝒱.pullback c k).U0 ∧ Nonempty (𝒱.pullback c k).U1 := by sorry
