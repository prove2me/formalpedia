-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
-- name    : AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/54303409-8930-5f50-8c4d-c52c33c54482
-- title:
--   Injectivity at affine limits for the Pic⁰ subpresheaf
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme with a morphism $c\colon C\to\operatorname{Spec}R$, let $\mathcal V$ be a two-affine open cover of $C$, that is, two open subschemes $U_0,U_1$ of $C$, both affine, with $U_0\sqcup U_1=\top$ and $U_0\cap U_1$ affine, and let $\varepsilon$ be a section of $c$ over $\operatorname{Spec}R$, i.e. a morphism $\varepsilon\colon\operatorname{Spec}R\to C$ with $\varepsilon$ followed by $c$ equal to the identity. Consider the subpresheaf of the rigidified relative Picard presheaf of $(c,\varepsilon)$ on $(\mathrm{Over}\ \operatorname{Spec}R)^{\mathrm{op}}$ cut out by the condition `algEquivZeroCut`: a class at $t\colon T\to\operatorname{Spec}R$ is admitted when it is represented by a rigidified line bundle $M$ such that for every algebraically closed field $k$ and every $s\colon\operatorname{Spec}k\to T$ the pullback of $M.L$ to the fibre `fibreAt c t s` satisfies `IsAlgEquivZero`. The assertion is `IsLFPInj` for this presheaf $G$: for every $R$-algebra $A$, every finitely generated $R$-subalgebra $A_0\subseteq A$ and all $x_0,x_0'\in G(\operatorname{Spec}A_0)$ whose restrictions along $\operatorname{Spec}A\to\operatorname{Spec}A_0$ coincide, there exist a finitely generated $R$-subalgebra $A_1$ with $A_0\le A_1\subseteq A$ such that $x_0$ and $x_0'$ already have equal restrictions along $\operatorname{Spec}A_1\to\operatorname{Spec}A_0$.
--
--   This is the injectivity half of the passage to a filtered limit of affine bases for the relative $\mathrm{Pic}^0$ functor of a pointed curve-like morphism, in the form where the existence of a cover by two affine opens with affine intersection is taken as a hypothesis rather than deduced from smoothness and properness. It is used in the construction of open charts for $\mathrm{Pic}^0$ from polarisations and from relative effective Cartier divisors with fibrewise vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra AlgebraicGeometry.AffineLimit

theorem AlgebraicGeometry.RelPicard.isLFPInj_relSubPicPresheaf_algEquivZeroCut_of_twoAffineOpenCover
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (𝒱 : C.TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    IsLFPInj (relSubPicPresheaf c ε (algEquivZeroCut c ε)) := by sorry
