-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/49573b92-974f-58f8-a164-283da3091f1d
-- title:
--   Norm-of-pullback endomorphism of relative Pic⁰ is a homomorphism
-- statement:
--   Let $R$ be a commutative ring, $c : C \to \operatorname{Spec} R$ a scheme over $R$ equipped with a section $\varepsilon$ (a morphism $\operatorname{Spec} R \to C$ with $\varepsilon \circ c = \mathrm{id}$), and let $D$ consist of a scheme together with a structure morphism `D.toBase` to $\operatorname{Spec} R$ and a section `D.zeroSection`. Assume $h$ exhibits $D$ as representing the cut `algEquivZeroCut c ε`: $D$ carries a rigidified line bundle $\mathcal{P}$ on $\operatorname{pullback} c\,$`D.toBase`, fibrewise algebraically equivalent to zero, such that every rigidified line bundle over any $t : T \to \operatorname{Spec} R$ satisfying the same fibrewise condition is, up to isomorphism of underlying modules, the pullback of $\mathcal{P}$ along a unique $t$-point of $D$, and the pullback of $\mathcal{P}$ along `D.zeroSection` is trivial. Let $cE : E \to \operatorname{Spec} R$ and $\varphi, \psi : E \to C$ with $\varphi \circ c = cE = \psi \circ c$ (written in Lean as $\varphi \gg c = cE$, $\psi \gg c = cE$), with $\varphi$ finite, flat and locally of finite presentation of constant fibre rank $d$ at every point of $C$. Let $u$ be an endomorphism of $D$ over $\operatorname{Spec} R$, i.e. a morphism with $u \circ$ `D.toBase` $=$ `D.toBase`, and suppose that for every $t : S \to \operatorname{Spec} R$ and every $t$-point $b$ of $D$ the pullback of $\mathcal{P}$ along $u \circ b$ has underlying module isomorphic to $$N \otimes (\operatorname{pullback} c\,t \to S)^{*}\bigl(\text{(unit-section restriction of } N)^{\vee}\bigr),$$ the rigidification along `rigSection c t ε` of $N = \det_d(\pi_{*}M) \otimes \det_d(\pi_{*}\mathcal{O})^{\vee}$, where $\pi$ is the base change of $\varphi$ to $t$ and $M$ is the pullback along the base change of $\psi$ of the module underlying $\mathcal{P}|_b$. Then, first, for every $s : S \to \operatorname{Spec} R$ and all $s$-points $x, y$ of $D$ one has $u \circ (x \cdot y) = (u \circ x) \cdot (u \circ y)$, where $\cdot$ is the relative group law on points of $D$ induced by $h$ for the group cut `algEquivZeroGroupCut c ε`; and second, `D.zeroSection` followed by $u$ equals `D.zeroSection`.
--
--   This is the statement that an endomorphism of a relative $\mathrm{Pic}^0$ which, on points, computes the norm along a finite flat map $\varphi$ of the pullback along $\psi$ of a line bundle class — i.e. the endomorphism attached to the correspondence $(\varphi,\psi)$ — respects the group law and fixes the origin, no representing object being assumed for the source curve $E$. It is used in the construction of Hecke-type descent for the Jacobian of $X_1(p)$, where $E$ arises as the preimage of a component under a degeneracy map and may be singular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.schemeHomOverComp_mul_eq_mul_and_zeroSection_comp_of_classifies_normModule_pullback
    {R : Type u} [CommRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

    {E : Scheme.{u}} (cE : E ⟶ Spec (CommRingCat.of R)) (φ ψ : E ⟶ C) (hφ : φ ≫ c = cE) (hψ : ψ ≫ c = cE)
    [IsFinite φ] [Flat φ] [LocallyOfFinitePresentation φ] (d : ℕ) (hd : ∀ x : C, φ.finrank x = d)

    (u : SchemeHomOver D.toBase D.toBase)
    (hu : ∀ {S : Scheme.{u}} (t : S ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t D.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b u)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange (c := c) (c' := cE) φ hφ t) d
            ((Scheme.Modules.pullback (curveChange (c := c) (c' := cE) ψ hψ t)).obj (h.poincare.pullbackAlong b).L)))) :
    (∀ {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s x y) u =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul s
            (NeronModelInfra.schemeHomOverComp x u) (NeronModelInfra.schemeHomOverComp y u)) ∧
      D.zeroSection ≫ u.1 = D.zeroSection := by sorry
