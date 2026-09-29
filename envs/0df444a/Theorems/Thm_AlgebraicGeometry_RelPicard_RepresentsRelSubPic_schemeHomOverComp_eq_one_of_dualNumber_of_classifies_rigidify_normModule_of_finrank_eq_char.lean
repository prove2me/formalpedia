-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/f039cc9e-9f86-50fd-9abd-dfe33cbcf0cd
-- title:
--   Norm morphism sends dual-number points over the origin to the origin
-- statement:
--   Let $\kappa$ be an algebraically closed field of characteristic $p$ with $p$ prime, and let $C$, $C'$ be integral schemes with structure morphisms $c : C \to \operatorname{Spec}\kappa$, $c' : C' \to \operatorname{Spec}\kappa$, where $c$ is locally of finite type; $\mathcal{V}$ is a datum of two affine opens of $C$ covering $C$ and having affine intersection, and `hC` asks that every closed subset of $C$ other than all of $C$ be finite. Let $\varepsilon$, $\varepsilon'$ be sections of $c$, $c'$, and let $D$, $D'$ consist of schemes with a morphism to $\operatorname{Spec}\kappa$ and a zero section thereof; $h$, $h'$ assert that $D$, $D'$ carry Poincaré rigidified invertible modules representing, over $\kappa$-schemes, the functor of $\varepsilon$- (resp. $\varepsilon'$-) rigidified invertible modules on the base change of $C$ (resp. $C'$) that are algebraically equivalent to zero on every geometric fibre, the pullback along the zero section being trivial. Let $\pi : C' \to C$ satisfy $\pi \circ c' \mathrel{=}$, in diagrammatic order, $\pi$ followed by $c$ equal to $c'$, with $\pi$ finite, flat and locally of finite presentation, of rank $p$ at every point of $C$, and injective on closed points. Let $N$ be a morphism from the scheme of $D'$ to that of $D$ over $\operatorname{Spec}\kappa$, and assume `hN`: for every $t : T \to \operatorname{Spec}\kappa$ and every $T$-point $a$ of $D'$ over $t$, the bundle obtained by pulling the Poincaré bundle of $D$ back along $a$ followed by $N$ is isomorphic to the rigidification, along the section $\mathrm{rigSection}\,c\,t\,\varepsilon$ and the projection $\mathrm{pullback.snd}\,c\,t$, of the norm module $\det_p(\pi_{T*}L) \otimes \det_p(\pi_{T*}\mathcal{O})^{\vee}$ of the bundle $L$ classified by $a$, $\pi_T$ being the base change of $\pi$ to $T$. Finally let $u$ be a point of $D'$ with values in the dual numbers $\mathrm{DualNumber}\,\kappa$, lying over the structure map $\operatorname{Spec}\mathrm{DualNumber}\,\kappa \to \operatorname{Spec}\kappa$, and assume that restricting $u$ along $\operatorname{Spec}$ of the projection $\mathrm{DualNumber}\,\kappa \to \kappa$ gives the unit $\kappa$-point of the group law on $D'$ attached to $h'$. The conclusion is that $u$ followed by $N$ equals the unit point of the group law on $D$ attached to $h$ at the structure map $\operatorname{Spec}\mathrm{DualNumber}\,\kappa \to \operatorname{Spec}\kappa$.
--
--   This is the statement that the differential at the origin of a morphism of relative $\operatorname{Pic}^0$ schemes classifying the norm along a finite flat degree-$p$ cover, injective on closed points, vanishes: every tangent vector at the identity is sent to the identity. It is used in the treatment of Frobenius-type endomorphisms on Jacobians of modular curves, being cited by [`ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber`](thm.html#ModularCurve.DRModelPackageLevel.schemeHomOverComp_frob_eq_of_dualNumber).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_eq_one_of_dualNumber_of_classifies_rigidify_normModule_of_finrank_eq_char
    {κ : Type u} [Field κ] [IsAlgClosed κ] {p : ℕ} [Fact p.Prime] [CharP κ p]
    {C C' : Scheme.{u}} [IsIntegral C] [IsIntegral C']
    {c : C ⟶ Spec (CommRingCat.of κ)} {c' : C' ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType c] (𝒱 : C.TwoAffineOpenCover)

    (hC : ∀ Z : Set C, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) c'}
    {D : RelativePic0Designation κ c} {D' : RelativePic0Designation κ c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (hd : ∀ x : C, π.finrank x = p)
    (hinj : ∀ x₁ x₂ : C', IsClosed ({x₁} : Set C') → IsClosed ({x₂} : Set C') → π.base x₁ = π.base x₂ → x₁ = x₂)

    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of κ)) (a : SchemeHomOver t D'.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange π hπ t) p (h'.poincare.pullbackAlong a).L)))

    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) D'.toBase)
    (hu : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ).toRingHom) ≫ u.1 =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').one (𝟙 _)).1) :
    NeronModelInfra.schemeHomOverComp u N =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
        (Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))) := by sorry
