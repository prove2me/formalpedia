-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/97e6151e-747c-53ad-921a-fbecb4f129e2
-- title:
--   Restricting a finite flat correspondence endomorphism along ν
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a scheme over $R$ and $\varepsilon$ a section of $c$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$); let $D$ be a relative $\mathrm{Pic}^0$ designation for $c$, i.e. a scheme $D.P$ with structure morphism $D.\mathtt{toBase}$ to $\operatorname{Spec} R$ and a zero section, and let $h$ witness that $D$ represents, with Poincaré bundle $h.\mathtt{poincare}$, the functor of $\varepsilon$-rigidified invertible modules on $C \times_R T$ that are fibrewise algebraically equivalent to zero (over algebraically closed fields), the universal property being unique classification of every such bundle by a $T$-point of $D$ over $R$. Let $y : Y \to \operatorname{Spec} R$ and $\pi_\alpha, \pi_\beta : Y \to C$ satisfy $\pi_\alpha \circ c = \pi_\beta \circ c = y$ (diagrammatically, $\pi_\alpha \gg c = y$ and likewise for $\pi_\beta$), with $\pi_\alpha$ finite, flat and locally of finite presentation and $\pi_\alpha.\mathtt{finrank}\,x = d$ at every point $x$ of $C$. Let $T$ be an endomorphism of $D.P$ over $\operatorname{Spec} R$ such that for every $t : S \to \operatorname{Spec} R$ and every $S$-point $a$ of $D$ over $t$, the pullback of the Poincaré bundle along $a$ followed by $T$ is isomorphic to $\mathtt{rigidify}$ along $\mathtt{rigSection}\,c\,t\,\varepsilon$ and $\mathrm{pr}_2 : C \times_R S \to S$ — that is, $L \mapsto L \otimes \mathrm{pr}_2^{*}\bigl((\mathtt{rigSection}^{*}L)^{\vee}\bigr)$ — of $\mathtt{normModule}$ of the base change of $\pi_\alpha$ in degree $d$, namely $\det_d(\pi_{\alpha *}(-)) \otimes \det_d(\pi_{\alpha *}\mathcal{O})^{\vee}$, applied to the pullback along the base change of $\pi_\beta$ of the bundle classified by $a$. Let $(C_a, \varepsilon_a, D_a, h_a)$ be a second such datum over $R$, $i : C_a \to C$ with $i \circ c = c_a$, and $\nu : D.P \to D_a.P$ over $\operatorname{Spec} R$ such that for all $t$ and all $a$ as above, the pullback of the second Poincaré bundle along $a$ followed by $\nu$ is isomorphic to the $\varepsilon_a$-rigidification of the pullback along the base change of $i$ of the bundle classified by $a$. Finally let $e : Y \times_{\pi_\alpha, C, i} C_a \to C_a$ satisfy $e \circ i = \mathrm{pr}_Y \circ \pi_\beta$ and $e \circ c_a = \mathrm{pr}_{C_a} \circ c_a$. Then there exists an endomorphism $u$ of $D_a.P$ over $\operatorname{Spec} R$ such that, first, for every $t : S \to \operatorname{Spec} R$ and every $S$-point $b$ of $D_a$ over $t$, the pullback of the second Poincaré bundle along $b$ followed by $u$ is isomorphic to the $\varepsilon_a$-rigidification of the degree-$d$ $\mathtt{normModule}$ of the base change of $\mathrm{pr}_{C_a} : Y \times_C C_a \to C_a$ applied to the pullback along the base change of $e$ of the bundle classified by $b$; and second, for every $t$ and every $S$-point $a$ of $D$ over $t$, the composites $(a \text{ then } T) \text{ then } \nu$ and $(a \text{ then } \nu) \text{ then } u$ agree as $S$-points of $D_a$ over $t$.
--
--   This is the statement that the endomorphism of a relative $\mathrm{Pic}^0$ defined by a finite flat correspondence $(\pi_\alpha, \pi_\beta)$ on $C$ restricts, along a morphism $i : C_a \to C$ that the correspondence carries into itself, to the endomorphism defined by the restricted correspondence $(\mathrm{pr}_{C_a}, e)$ on $C_a$, the two being intertwined by $\nu$. It is used in the treatment of Hecke operators on Jacobians of modular curves, where the restricted operator is needed on a single component of a special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_normModule_pullback_and_schemeHomOverComp_eq_of_comp_eq
    {R : Type u} [CommRing R]

    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) (πα πβ : Y ⟶ C) (Hα : πα ≫ c = y) (Hβ : πβ ≫ c = y)
    [IsFinite πα] [Flat πα] [LocallyOfFinitePresentation πα] (d : ℕ) (hd : ∀ x : C, πα.finrank x = d)

    (T : SchemeHomOver D.toBase D.toBase)
    (hT : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a T)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange (c' := y) πα Hα t) d
            ((Scheme.Modules.pullback (curveChange (c' := y) πβ Hβ t)).obj (h.poincare.pullbackAlong a).L))))

    {Ca : Scheme.{u}} (ca : Ca ⟶ Spec (CommRingCat.of R)) (εa : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) ca)
    (Da : RelativePic0Designation R ca) (ha : RepresentsRelSubPic ca εa (algEquivZeroCut ca εa) Da)
    (i : Ca ⟶ C) (hi : i ≫ c = ca)

    (ν : SchemeHomOver D.toBase Da.toBase)
    (hν : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν)).L ≅
        Scheme.Modules.rigidify (rigSection ca t εa) (pullback.snd ca t)
          ((Scheme.Modules.pullback (curveChange i hi t)).obj (h.poincare.pullbackAlong a).L)))

    (e : pullback πα i ⟶ Ca) (he : e ≫ i = pullback.fst πα i ≫ πβ)
    (he' : e ≫ ca = pullback.snd πα i ≫ ca) :
    ∃ u : SchemeHomOver Da.toBase Da.toBase,
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t Da.toBase),
        Nonempty ((ha.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
          Scheme.Modules.rigidify (rigSection ca t εa) (pullback.snd ca t)
            (Scheme.Modules.normModule
              (curveChange (c := ca) (c' := pullback.snd πα i ≫ ca) (pullback.snd πα i) rfl t) d
              ((Scheme.Modules.pullback
                  (curveChange (c := ca) (c' := pullback.snd πα i ≫ ca) e he' t)).obj
                (ha.poincare.pullbackAlong b).L)))) ∧
      (∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a T) ν =
          NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp a ν) u) := by sorry
