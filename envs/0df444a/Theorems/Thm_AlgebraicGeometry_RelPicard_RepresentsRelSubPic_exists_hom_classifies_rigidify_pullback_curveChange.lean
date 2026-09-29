-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/bcdc3021-d873-5679-9712-fb5ba6eb5771
-- title:
--   Pullback along a non-pointed curve morphism induces a Pic⁰-homomorphism
-- statement:
--   Let $R$ be a commutative ring and let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$, equipped with sections $\varepsilon$ of $c$ and $\varepsilon'$ of $c'$ (morphisms $\operatorname{Spec} R \to C$, resp. $\to C'$, composing with $c$, resp. $c'$, to the identity). Let $f : C' \to C$ satisfy $c \circ f = c'$; no compatibility of $f$ with $\varepsilon, \varepsilon'$ is assumed. Let $D$ and $D'$ be designations, each consisting of a scheme with a structure morphism `toBase` to $\operatorname{Spec} R$ and a section `zeroSection`, and let $h$, $h'$ witness that $D$ represents the cut `algEquivZeroCut c ε` and $D'$ the cut `algEquivZeroCut c' ε'`: that is, $h$ provides a rigidified line bundle `h.poincare` on $C \times_{\operatorname{Spec} R} D$ satisfying `FibrewiseAlgEquivZero`, such that for every $t : T \to \operatorname{Spec} R$ every $\varepsilon$-rigidified line bundle on $C \times_{\operatorname{Spec} R} T$ satisfying `FibrewiseAlgEquivZero` is isomorphic to the pullback of `h.poincare` along a unique $T$-point of $D$ over $R$, with the pullback along `zeroSection` isomorphic to the unit; likewise for $h'$, $\varepsilon'$, $c'$, $D'$. The assertion is that there exists a morphism $N$ from $D$ to $D'$ over $\operatorname{Spec} R$ such that: (i) for every $t : T \to \operatorname{Spec} R$ and every $T$-point $a$ of $D$ over $R$, the line bundle underlying the pullback of `h'.poincare` along $a$ followed by $N$ is isomorphic to the rigidification, in the sense $L \mapsto L \otimes \mathrm{pr}_T^{*}((\mathrm{rig}_{\varepsilon'})^{*}L)^{\vee}$ along the section `rigSection c' t ε'` and the projection $C' \times_{\operatorname{Spec} R} T \to T$, of the pullback of $(a^{*}\,\mathrm{h.poincare}).L$ along $f \times \mathrm{id}_T$; (ii) composition with $N$ is multiplicative for the group laws on $T$-points furnished by $h$ and $h'$ for the group cuts `algEquivZeroGroupCut c ε` and `algEquivZeroGroupCut c' ε'`; and (iii) `D.zeroSection` followed by $N$ equals `D'.zeroSection`.
--
--   This is the functoriality of the relative Picard scheme (its fibrewise algebraically trivial part) under an arbitrary $R$-morphism of curves, re-rigidified along the section of the target so that pullback of line bundles becomes an operation on rigidified bundles; the classifying morphism is then a homomorphism of group objects sending zero to zero. It is the form needed when the morphism does not respect the chosen sections, and is used to construct Atkin–Lehner and degeneracy morphisms on Jacobians of modular curves and their base changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c')
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D') :
    ∃ N : SchemeHomOver D.toBase D'.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
          Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
            ((Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      D.zeroSection ≫ N.1 = D'.zeroSection := by sorry
