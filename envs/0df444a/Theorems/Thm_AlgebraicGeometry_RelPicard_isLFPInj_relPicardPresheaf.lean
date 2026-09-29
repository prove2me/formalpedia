-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf
-- name    : AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/5411f3bd-5916-5328-875f-f9b24e5caef8
-- title:
--   Affine-limit injectivity of the rigidified relative Picard presheaf
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme, let $c \colon C \to \operatorname{Spec} R$ be a morphism, let $\mathcal V$ be a `TwoAffineOpenCover` of $C$, that is, two open subschemes $U_0, U_1$ of $C$ which are affine, whose union is all of $C$ and whose intersection is affine, and let $\varepsilon$ be an element of `SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c`, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Consider the presheaf `relPicardPresheaf c ε` on the opposite of the category of schemes over $\operatorname{Spec} R$, which sends an object $t \colon T \to \operatorname{Spec} R$ to the quotient of the type of rigidified line bundles on $C \times_{\operatorname{Spec} R} T$ — invertible modules $L$ together with a nonempty set of isomorphisms between the pullback of $L$ along the section determined by $\varepsilon$ and the unit module — by the isomorphism relation, with functoriality given by pullback. The theorem asserts the predicate `AffineLimit.IsLFPInj` for this presheaf: for every $R$-algebra $A$, every finitely generated $R$-subalgebra $A_0 \subseteq A$ and any two classes $x_0, x_0'$ over $\operatorname{Spec} A_0$, if the pullbacks of $x_0$ and $x_0'$ along $\operatorname{Spec} A \to \operatorname{Spec} A_0$ coincide, then there is a finitely generated $R$-subalgebra $A_1$ with $A_0 \le A_1 \le A$ such that the pullbacks of $x_0$ and $x_0'$ along $\operatorname{Spec} A_1 \to \operatorname{Spec} A_0$ already coincide.
--
--   This is the injectivity half of the assertion that the rigidified relative Picard functor of $c \colon C \to \operatorname{Spec} R$ is locally of finite presentation, i.e. commutes with filtered colimits of $R$-algebras, here for a base curve or relative curve admitting a cover by two affine opens with affine intersection. It is used in the Néron model infrastructure, in the corresponding affine-limit injectivity statements for the relative sub-Picard presheaf cut out by an algebra isomorphism condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isLFPInj_relPicardPresheaf.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_AffineLimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.isLFPInj_relPicardPresheaf
    (R : Type u) [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    AffineLimit.IsLFPInj (relPicardPresheaf c ε) := by sorry
