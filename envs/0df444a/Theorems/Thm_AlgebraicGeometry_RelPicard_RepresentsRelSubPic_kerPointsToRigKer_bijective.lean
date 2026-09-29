-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_bijective
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/8843269e-3f87-575f-bfb4-11a66a693e22
-- title:
--   Dual-number kernel points classify rigidified bundles trivial modulo ε
-- statement:
--   Let $R$ be a commutative ring, let $C$ be a scheme with a structure morphism $c : C \to \operatorname{Spec} R$, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $D$ consist of a scheme $P$, a morphism $D.\mathrm{toBase} : P \to \operatorname{Spec} R$ and a section $D.\mathrm{zeroSection}$ of it. Assume $h$ witnesses that $D$ represents the rigidified relative Picard functor cut out by `algEquivZeroCut c ε`: a Poincaré rigidified line bundle on $C \times_R P$ satisfying, for every algebraically closed field $k$ and every $k$-point of $P$, the condition `IsAlgEquivZero` on the corresponding fibre; the universal property that every rigidified line bundle $M$ on $C \times_R T$ ($T$ over $\operatorname{Spec} R$) satisfying that fibrewise condition is, for a unique morphism $T \to P$ over $\operatorname{Spec} R$, the pullback of the Poincaré bundle up to isomorphism of underlying modules; and triviality of the pullback along the zero section. Let $A$ be an $R$-algebra. Then the map `h.kerPointsToRigKer A` is bijective: on morphisms $x : \operatorname{Spec} A[\varepsilon] \to P$ over $\operatorname{Spec} R$ whose composite with the reduction $\operatorname{Spec} A \to \operatorname{Spec} A[\varepsilon]$ is the unit section of the relative group law induced by $h$, sending $x$ to the class in `RigKerDualNumber c ε A` of the pullback of the Poincaré bundle along $x$.
--
--   This identifies the kernel of $D(A[\varepsilon]) \to D(A)$ with the kernel of the rigidified Picard group map $\operatorname{Pic}^{\mathrm{rig}}(C_{A[\varepsilon]}) \to \operatorname{Pic}^{\mathrm{rig}}(C_A)$, the functorial form of the computation of the tangent space of the relative Picard scheme along the zero section. It is used for the additivity and naturality of the resulting deformation-class bijection and for the base-change statements about kernel points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_kerPointsToRigKer_bijective.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.kerPointsToRigKer_bijective
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective (h.kerPointsToRigKer A) := by sorry
