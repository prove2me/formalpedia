-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
-- name    : AlgebraicCurve.CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/1f58f3eb-e1eb-54ab-b2ad-1e41d62e7fd0
-- title:
--   Formal unramifiedness near a rational point gives ramification index one
-- statement:
--   Let $K$ be an algebraically closed field and let $L$, $L'$ be field extensions of $K$. Let $M$ and $M'$ be curve models over $K$ of $L$ and of $L'$ respectively, that is, integral schemes $M.C$, $M'.C$ with proper, smooth of relative dimension $1$ structure morphisms to $\operatorname{Spec} K$, together with ring isomorphisms $\mathrm{ffEquiv}$ from $L$ (resp. $L'$) onto the function field of $M.C$ (resp. $M'.C$) compatible with $K$, a bijection from the closed points onto the places of $L$ (resp. $L'$) over $K$ under which the image of the local ring in the function field is the corresponding valuation subring, and the property that every finite set of points lies in an affine open. Let $\varphi : L' \to L$ be a $K$-algebra map which is integral as a ring homomorphism, and let $\pi_M : M.C \to M'.C$ be a morphism over $\operatorname{Spec} K$ (i.e. $\pi_M$ followed by $M'.\mathrm{toBase}$ equals $M.\mathrm{toBase}$) whose behaviour at the generic points is given by $\varphi$: the canonical morphism from the spectrum of the stalk of $M.C$ at its generic point, followed by $\pi_M$, equals $\operatorname{Spec}$ of $\mathrm{ffEquiv}_M \circ \varphi \circ \mathrm{ffEquiv}_{M'}^{-1}$ followed by the canonical morphism from the spectrum of the stalk of $M'.C$ at its generic point. Let $y$ be a $K$-point of $M.C$, i.e. a section $\operatorname{Spec} K \to M.C$ of $M.\mathrm{toBase}$, let $V$ be an open subscheme of $M.C$ whose underlying set contains the image of the closed point of $\operatorname{Spec} K$ under $y$, and assume that the inclusion of $V$ followed by $\pi_M$ is formally unramified. Then the ramification index of the place of $L$ attached to $y$ along $\varphi$ equals $1$; that is, the least positive integer of the form $\operatorname{ord}_w(\varphi f)$ with $0 \neq f \in L'$, where $w$ is the place corresponding to $y$ under the bijection between $K$-points of $M.C$ and places of $L$ over $K$, is $1$.
--
--   This is the familiar statement that an unramified morphism of smooth curves induces an unramified extension of the corresponding local rings, here in the form $e = 1$ for the place attached to a rational point. It is used in the ramification bookkeeping for degeneracy maps between modular curve models, being cited by [`ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified`](thm.html#ModularCurve.XHDRModelAtP.ramificationIndexAlong_degeneracyEmb_pointEquivPlace_eq_one_of_formallyUnramified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.CurveModel.ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified
    {K : Type u} [Field K] [IsAlgClosed K]
    {L : Type u} [Field L] [Algebra K L] {L' : Type u} [Field L'] [Algebra K L']
    (M : CurveModel K L) (M' : CurveModel K L')
    (φ : L' →ₐ[K] L) (hφ : φ.toRingHom.IsIntegral)
    (πM : M.C ⟶ M'.C) (hπM : πM ≫ M'.toBase = M.toBase)
    (hgen : M.C.fromSpecStalk (genericPoint M.C) ≫ πM =
      Spec.map (CommRingCat.ofHom (M.ffEquiv.toRingHom.comp (φ.toRingHom.comp M'.ffEquiv.symm.toRingHom))) ≫
        M'.C.fromSpecStalk (genericPoint M'.C))
    (y : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (V : M.C.Opens) (hyV : y.1.base (IsLocalRing.closedPoint K) ∈ V)
    (hV : FormallyUnramified (V.ι ≫ πM)) :
    Place.ramificationIndexAlong φ (M.pointEquivPlace y) = 1 := by sorry
