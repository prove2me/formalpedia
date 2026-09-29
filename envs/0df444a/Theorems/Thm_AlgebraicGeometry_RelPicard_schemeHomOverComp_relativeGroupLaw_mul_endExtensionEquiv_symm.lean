-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
-- name    : AlgebraicGeometry.RelPicard.schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/4f957f0f-602e-55bb-8b24-ae5669e743f6
-- title:
--   Néron extension of an endomorphism preserves the group law
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain) with field $K$ realised as its fraction field, let $c \colon C \to \operatorname{Spec} R$ be a scheme over $R$ and $\varepsilon$ a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ composing with $c$ to the identity. Let $D$ consist of a scheme with structure morphism $D.\mathrm{toBase}$ to $\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents the rigidified relative Picard functor of $(c,\varepsilon)$ cut out by the condition `FibrewiseAlgEquivZero`: a Poincaré rigidified line bundle satisfying that condition, every such bundle over a test base being the pullback of the Poincaré bundle along a unique point of $D$, with the zero section giving the unit. Assume $D.\mathrm{toBase}$ smooth and separated, that `NeronModelPropertyBundle R K D.toBase` holds (smooth, separated, locally of finite type, quasi-compact, and the unique-extension property `NeronUniqueExtension` for $R \subset K$), that $h'$ is analogous representing data over $K$ for the base-changed pair, on the designation obtained as the pullback of $D.\mathrm{toBase}$ along $\operatorname{Spec} K \to \operatorname{Spec} R$, and that its Poincaré bundle is isomorphic to the transport to $K$ of the pullback of that of $h$ along the first projection. Let $\varphi_\eta$ be an endomorphism of the base-changed $D$ over $\operatorname{Spec} K$ which, on $T$-points for every $K$-scheme $T$, is a homomorphism for the relative group law attached to $h'$ via the group-theoretic cut `algEquivZeroGroupCut`. Then the endomorphism of $D$ over $\operatorname{Spec} R$ obtained from $\varphi_\eta$ by the inverse of the generic-fibre restriction bijection supplied by the Néron property is likewise a homomorphism: for every $s \colon T \to \operatorname{Spec} R$ and all $T$-points $x,y$ of $D$, composing the product of $x$ and $y$ with it equals the product of the two composites.
--
--   This is the statement that an endomorphism of the generic fibre which respects the group law extends, by the Néron mapping property, to an endomorphism of the whole relative $\mathrm{Pic}^0$ respecting its group law. It is used in the construction of Hecke endomorphisms of relative Jacobians of models of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

set_option maxHeartbeats 800000 in

theorem AlgebraicGeometry.RelPicard.schemeHomOverComp_relativeGroupLaw_mul_endExtensionEquiv_symm
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsSeparated D.toBase]
    (hN : NeronModelPropertyBundle R K D.toBase)
    (h' : RepresentsRelSubPic (baseChange R c K) (sectionBaseChange K ε)
      (algEquivZeroCut (baseChange R c K) (sectionBaseChange K ε)) (D.baseChange K))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε K
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R K), pullback.condition⟩)).L))
    (φη : SchemeHomOver (D.baseChange K).toBase (D.baseChange K).toBase)
    (hhom : ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver s (D.baseChange K).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw
            (P := algEquivZeroGroupCut (baseChange R c K) (sectionBaseChange K ε)) h').mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη)) :
    ∀ {T : Scheme.{u}} (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y)
          (hN.endExtensionEquiv.symm φη) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
          (NeronModelInfra.schemeHomOverComp x (hN.endExtensionEquiv.symm φη))
          (NeronModelInfra.schemeHomOverComp y (hN.endExtensionEquiv.symm φη)) := by sorry
