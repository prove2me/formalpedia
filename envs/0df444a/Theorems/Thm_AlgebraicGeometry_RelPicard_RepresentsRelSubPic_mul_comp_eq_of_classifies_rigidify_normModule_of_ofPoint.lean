-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/b8e0ca72-8f12-5870-a974-0b6bc1d9f574
-- title:
--   Norm morphism of relative Pic⁰ and Abel–Jacobi classes
-- statement:
--   Let $R$ be a commutative ring, and let $c : C \to \operatorname{Spec} R$ and $c' : C' \to \operatorname{Spec} R$ be separated, with sections $\varepsilon, \varepsilon'$ (morphisms $\operatorname{Spec} R \to C$, resp. $\to C'$, splitting $c$, resp. $c'$). Let $D, D'$ be pointed $R$-schemes $(P \to \operatorname{Spec} R$ with a zero section$)$, and let $h$, $h'$ witness that they represent, via rigidified Poincaré bundles, the functor of rigidified line bundles on $C \times_R T$, resp. $C' \times_R T$, whose pullback to every fibre over an algebraically closed field is algebraically equivalent to zero: for each such bundle $M$ over $t : T \to \operatorname{Spec} R$ there is a unique $T$-point of $D$ (resp. $D'$) along which the Poincaré bundle pulls back to $M$. Let $\pi : C' \to C$ satisfy $\pi \circ c = c'$ and be finite, flat and locally of finite presentation with $\operatorname{finrank}_\pi \equiv d$. Let $N : D' \to D$ be an $R$-morphism classifying the norm along $\pi$: for every $t : T \to \operatorname{Spec} R$ and every $T$-point $a$ of $D'$, the Poincaré bundle of $D$ pulled back along $a$ followed by $N$ is isomorphic to the rigidification along the graph of $t \circ \varepsilon$ (tensoring with the pullback under $C\times_R T \to T$ of the dual of the restriction) of $\det{}_d(\pi_{T*}L) \otimes \det{}_d(\pi_{T*}\mathcal{O})^{\vee}$, where $L$ is the pullback of the Poincaré bundle of $D'$ along $a$ and $\pi_T$ is the base change of $\pi$. Let $K$ be a field and $t : \operatorname{Spec} K \to \operatorname{Spec} R$ a point over which $C \times_R \operatorname{Spec} K$ and $C' \times_R \operatorname{Spec} K$ are smooth of relative dimension $1$. Let $y$ be a $K$-point of $C'$ over $t$, and let $x_b, x_g$ be the $K$-points of $C$ given by $\pi \circ (t \circ \varepsilon')$ and $\pi \circ y$. Assume the $K$-point $a$ of $D'$ classifies $\mathcal{O}(y) \otimes \mathcal{I}(t\circ\varepsilon')$, the invertible module of the degree-one relative effective Cartier divisor cut out by the graph of $y$ tensored with the ideal module of the graph of $t \circ \varepsilon'$, and that the $K$-points $b, g$ of $D$ classify $\mathcal{O}(x_b) \otimes \mathcal{I}(t\circ\varepsilon)$ and $\mathcal{O}(x_g) \otimes \mathcal{I}(t\circ\varepsilon)$ respectively. Then, for the relative group law on $D$ induced by $h$ from the representability of the fibrewise-algebraically-trivial cut, the product at $t$ of $a$ followed by $N$ with $b$ equals $g$.
--
--   This is the norm (Albanese) functoriality of the Abel–Jacobi map in divisor-class form, $N_\pi(\mathrm{aj}'(y)) + \mathrm{aj}(\pi\varepsilon') = \mathrm{aj}(\pi y)$, stated purely in terms of the line bundles that the three points classify, with no Abel–Jacobi morphism in sight. It is used in the computation of degeneracy maps and of the Frobenius norm map on the relative Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint.lean

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
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

universe u

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_normModule_of_ofPoint
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} [IsSeparated c] [IsSeparated c']
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : C, π.finrank x = d)

    (N : SchemeHomOver D'.toBase D.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D'.toBase),
      Nonempty ((h.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t)
          (Scheme.Modules.normModule (curveChange π hπ t) d (h'.poincare.pullbackAlong a).L)))

    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] [SmoothOfRelativeDimension 1 (pullback.snd c' t)]

    (y : SchemeHomOver t c') (xb xg : SchemeHomOver t c) (hxb : xb.1 = (t ≫ ε'.1) ≫ π) (hxg : xg.1 = y.1 ≫ π)

    (a : SchemeHomOver t D'.toBase)
    (ha : Nonempty ((h'.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint c' y.1 y.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (b g : SchemeHomOver t D.toBase)
    (hb : Nonempty ((h.poincare.pullbackAlong b).L ≅
      (RelEffCartierDiv.ofPoint c xb.1 xb.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint c xg.1 xg.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul t
      (NeronModelInfra.schemeHomOverComp a N) b = g := by sorry
