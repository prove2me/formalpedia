-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/e189e710-fa81-5c6c-8319-c5e01b7da798
-- title:
--   Restriction morphism classifies the re-rigidified pullback bundle
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$, $c' : C' \to \operatorname{Spec} R$ be schemes over $R$, equipped with sections $\varepsilon$ of $c$ and $\varepsilon'$ of $c'$ (morphisms $\operatorname{Spec} R \to C$, resp. $C'$, splitting the structure morphisms). Let $f : C' \to C$ satisfy $f \circ c = c'$ (diagrammatically `f ≫ c = c'`) and $f \circ \varepsilon' = \varepsilon$. Let $D$, $D'$ be designations, each consisting of a scheme with a structure morphism to $\operatorname{Spec} R$ and a zero section, and let `h`, `h'` witness that $D$ represents the subfunctor of the $\varepsilon$-rigidified relative Picard functor of $c$ cut out by the predicate `FibrewiseAlgEquivZero`, and $D'$ the corresponding subfunctor for $c'$, $\varepsilon'$: each witness provides a Poincaré rigidified line bundle on the base change along the designation's own structure morphism satisfying that predicate, a unique-classification property for all rigidified bundles satisfying it, and triviality along the zero section. Then for every $t : T \to \operatorname{Spec} R$ and every $T$-point $a$ of $D$ over $\operatorname{Spec} R$, the underlying module of the pullback of $h'$'s Poincaré bundle along the composite of $a$ with `RepresentsRelSubPic.pullbackHom f hf hε h h'`, a morphism $D \to D'$, is isomorphic, on $C' \times_{\operatorname{Spec} R} T$, to $L \otimes q^{*}(\sigma^{*}L)^{\vee}$, where $L$ is the pullback of the bundle classified by $a$ along $f \times \mathrm{id}_T$, $\sigma$ is the section of $q = \mathrm{pr}_T$ induced by $\varepsilon'$.
--
--   This is the functoriality of the rigidified relative Picard functor in the pointed curve: it says that the restriction morphism $f^{*} : D \to D'$ between the representing schemes classifies, on $T$-points, the pullback along $f \times \mathrm{id}_T$ after re-rigidification along $\varepsilon'$. It is the form in which the classifying property is used downstream, for instance in the comparison of points of $D$ and $D'$ under $f^{*}$ and in statements about pullbacks of Poincaré bundles over a field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesRigidify

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_schemeHomOverComp_pullbackHom_iso_rigidify
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong
        (NeronModelInfra.schemeHomOverComp a (RepresentsRelSubPic.pullbackHom f hf hε h h'))).L ≅
      Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
        ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L)) := by sorry
