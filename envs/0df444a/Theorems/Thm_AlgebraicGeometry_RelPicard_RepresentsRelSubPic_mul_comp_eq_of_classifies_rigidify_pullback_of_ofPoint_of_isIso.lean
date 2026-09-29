-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
-- name    : AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/dd3eeb62-5b67-5f87-a95b-49170da9ef4d
-- title:
--   Curve isomorphism on Pic⁰ points: N(a)· b=g
-- statement:
--   Let $R$ be a commutative ring and let $c\colon C\to\operatorname{Spec}R$, $c'\colon C'\to\operatorname{Spec}R$ be separated morphisms equipped with sections $\varepsilon,\varepsilon'$ (morphisms $\operatorname{Spec}R\to C$, resp. $\to C'$, composing with $c$, resp. $c'$, to the identity). Let $D$, $D'$ be relative $\mathrm{Pic}^0$ designations for $c$, $c'$ — schemes over $\operatorname{Spec}R$ with a zero section — and let $h$, $h'$ be data representing the rigidified relative Picard functor cut out by the fibrewise algebraically-trivial condition `algEquivZeroCut`: a rigidified Poincaré bundle satisfying that condition, together with the universal property that every rigidified line bundle satisfying it on a base $t$ is, up to isomorphism, the pullback of the Poincaré bundle along a unique point of $D$ over $t$, plus triviality at the zero section. Let $\pi\colon C'\to C$ satisfy $\pi\circ{}$, in the sense $\pi$ followed by $c$ equals $c'$, and be an isomorphism. Let $N\colon D\to D'$ be a morphism over $\operatorname{Spec}R$ which classifies pullback along $\pi$: for every $t\colon T\to\operatorname{Spec}R$ and every point $a$ of $D$ over $t$, the pullback of the Poincaré bundle of $h'$ along $a$ followed by $N$ is isomorphic to the rigidification, along the section `rigSection c' t ε'` and the projection $\operatorname{pullback}(c',t)\to T$, of the pullback along `curveChange π hπ t` of $(h.\mathrm{poincare}.\mathrm{pullbackAlong}\,a).L$. Let $K$ be a field and $t\colon\operatorname{Spec}K\to\operatorname{Spec}R$ a point such that both base changes $\operatorname{pullback}(c,t)\to\operatorname{Spec}K$ and $\operatorname{pullback}(c',t)\to\operatorname{Spec}K$ are smooth of relative dimension $1$. Let $y$ be a $t$-point of $C$ and $y'$, $x_e$ $t$-points of $C'$ with $y'$ followed by $\pi$ equal to $y$, and $x_e$ followed by $\pi$ equal to $t$ followed by $\varepsilon$. Finally let $a$ be a point of $D$ over $t$ whose associated bundle is isomorphic to $\mathcal O(y)\otimes\mathcal I_{\varepsilon_t}$, i.e. the `lineBundle` (dual ideal module) of the degree-one relative effective Cartier divisor cut out by the graph of $y$, tensored with the `idealModule` of the graph divisor of $t\circ\varepsilon$; and let $b$, $g$ be points of $D'$ over $t$ whose associated bundles are isomorphic to $\mathcal O(x_e)\otimes\mathcal I_{\varepsilon'_t}$ and $\mathcal O(y')\otimes\mathcal I_{\varepsilon'_t}$ respectively. Then, in the relative group law on $D'$ obtained from $h'$ for the group cut `algEquivZeroGroupCut c' ε'`, the product at $t$ of the point $a$ followed by $N$ with $b$ equals $g$.
--
--   This is the $K$-point reading of functoriality of the rigidified relative $\mathrm{Pic}^0$ under an isomorphism of pointed curves: the homomorphism $N$ induced by pullback along $\pi$ sends the Abel–Jacobi class $[y-\varepsilon_t]$ to $[y'-\varepsilon'_t]-[x_e-\varepsilon'_t]$, stated in the equivalent form $N(a)\cdot b=g$. It is used to compute the effect of Atkin–Lehner and diamond operators on divisor classes of modular curves at a field-valued point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso.lean

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

theorem AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mul_comp_eq_of_classifies_rigidify_pullback_of_ofPoint_of_isIso
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)} [IsSeparated c] [IsSeparated c']
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (π : C' ⟶ C) (hπ : π ≫ c = c') [IsIso π]

    (N : SchemeHomOver D.toBase D'.toBase)
    (hN : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase),
      Nonempty ((h'.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a N)).L ≅
        Scheme.Modules.rigidify (rigSection c' t ε') (pullback.snd c' t)
          ((Scheme.Modules.pullback (curveChange π hπ t)).obj (h.poincare.pullbackAlong a).L)))

    {K : Type u} [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] [SmoothOfRelativeDimension 1 (pullback.snd c' t)]

    (y : SchemeHomOver t c) (y' xe : SchemeHomOver t c') (hy' : y'.1 ≫ π = y.1) (hxe : xe.1 ≫ π = t ≫ ε.1)

    (a : SchemeHomOver t D.toBase)
    (ha : Nonempty ((h.poincare.pullbackAlong a).L ≅
      (RelEffCartierDiv.ofPoint c y.1 y.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (b g : SchemeHomOver t D'.toBase)
    (hb : Nonempty ((h'.poincare.pullbackAlong b).L ≅
      (RelEffCartierDiv.ofPoint c' xe.1 xe.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule))
    (hg : Nonempty ((h'.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint c' y'.1 y'.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint c' (t ≫ ε'.1)
          ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε'.2).trans (Category.comp_id t)))).idealModule)) :
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c' ε') h').mul t
      (NeronModelInfra.schemeHomOverComp a N) b = g := by sorry
