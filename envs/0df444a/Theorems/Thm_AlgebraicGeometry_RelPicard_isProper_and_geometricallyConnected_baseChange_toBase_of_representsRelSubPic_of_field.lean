-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isProper_and_geometricallyConnected_baseChange_toBase_of_representsRelSubPic_of_field
-- name    : AlgebraicGeometry.RelPicard.isProper_and_geometricallyConnected_baseChange_toBase_of_representsRelSubPic_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/f4b572d3-db11-54f2-9eb4-49f30195c2db
-- title:
--   Properness and geometric connectedness of Pic⁰ after base change to a field
-- statement:
--   Let $R$ be a commutative ring, $C$ a scheme and $c \colon C \to \operatorname{Spec} R$ a morphism, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Let $D$ consist of a scheme $P$, a structure morphism $D.\mathrm{toBase} \colon P \to \operatorname{Spec} R$ and a section of it, and assume given $h$, the data exhibiting $D$ as representing the $\mathrm{Pic}^0$-cut of the rigidified relative Picard functor of $(c,\varepsilon)$: a rigidified invertible module (Poincaré bundle) on $C \times_{\operatorname{Spec} R} P$ that is fibrewise algebraically equivalent to zero (its pullback to $C_k$ along every point $\operatorname{Spec} k \to P$ with $k$ algebraically closed is algebraically equivalent to zero), such that for every $R$-scheme $t \colon T \to \operatorname{Spec} R$ and every rigidified invertible module $M$ on $C \times_{\operatorname{Spec} R} T$ with the same fibrewise property there is a unique $R$-morphism $T \to P$ pulling the Poincaré bundle back to something isomorphic to $M$, and such that the pullback along the zero section is trivial; $D.\mathrm{toBase}$ is assumed locally of finite type. Let $K$ be a field with an $R$-algebra structure, and assume the base change $C \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is proper, smooth of relative dimension $1$ and geometrically integral. Finally let $\mathcal{V}$ be a cover of $C$ by two affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Then the base-changed structure morphism $P \times_{\operatorname{Spec} R} \operatorname{Spec} K \to \operatorname{Spec} K$ is proper and geometrically connected.
--
--   This is the statement that, for a smooth proper geometrically integral curve over a field $K$ arising as the $K$-fibre of $(C,\varepsilon)$, the $K$-fibre of a scheme representing the $\mathrm{Pic}^0$-cut of the rigidified relative Picard functor is proper with geometrically connected fibres, i.e. is the Jacobian of $C_K$ as an abelian variety; no smoothness or properness is assumed of $c$ itself over $R$. It is the form of the Jacobian's properness and connectedness used for the modular curve models over $\mathbb{Q}$ and for the Néron-model and kernel-rank computations at $p$ in the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isProper_and_geometricallyConnected_baseChange_toBase_of_representsRelSubPic_of_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isProper_and_geometricallyConnected_baseChange_toBase_of_representsRelSubPic_of_field
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [LocallyOfFiniteType D.toBase]
    (K : Type u) [Field K] [Algebra R K]
    [IsProper (baseChange R c K)] [SmoothOfRelativeDimension 1 (baseChange R c K)]
    [GeometricallyIntegral (baseChange R c K)]
    (𝒱 : C.TwoAffineOpenCover) :
    IsProper (D.baseChange K).toBase ∧ GeometricallyConnected (D.baseChange K).toBase := by sorry
