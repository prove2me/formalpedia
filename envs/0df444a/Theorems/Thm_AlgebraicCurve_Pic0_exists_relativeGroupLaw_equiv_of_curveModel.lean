-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_relativeGroupLaw_equiv_of_curveModel
-- name    : AlgebraicCurve.Pic0.exists_relativeGroupLaw_equiv_of_curveModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f02c7381-5d68-5f6a-aa01-2825d199a944
-- title:
--   Existence of the Jacobian group scheme and Abel–Jacobi dictionary
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure satisfying `IsCurveOver K F`: every nonzero element of $F$ has an associated divisor of degree zero recording its orders at all places, each place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $M$ be a `CurveModel K F`, that is an integral scheme $M.C$ with a proper, smooth of relative dimension one morphism $M.\mathrm{toBase}\colon M.C \to \operatorname{Spec} K$, a ring isomorphism of $F$ with the function field of $M.C$ compatible with the structure map from $K$, a bijection from the closed points of $M.C$ to the places of $F/K$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open. Let $s$ be a section of $M.\mathrm{toBase}$, i.e. a $K$-point of the model. Then there exist a scheme $J$, a morphism $f\colon J \to \operatorname{Spec} K$, a relative group law $L$ on $f$ (functorial multiplication, unit and inverse on the sets $\{\varphi : T \to J \mid \varphi \text{ followed by } f = t\}$ for all $t\colon T \to \operatorname{Spec} K$, with associativity, unit and left-inverse laws and compatibility with base change), a morphism $aj\colon M.C \to J$ over $\operatorname{Spec} K$, and a bijection $\mathrm{pts}$ from $\mathrm{Pic}^0(F/K)$ — degree-zero divisors modulo principal ones — onto the sections of $f$, such that: $f$ is smooth and proper with every fibre $f^{-1}(\{x\})$ connected and admitting a relative group law; $L$ is commutative on $T$-points for every $t\colon T \to \operatorname{Spec} K$; $s$ followed by $aj$ is the unit section; $\mathrm{pts}$ carries addition to $L$-multiplication of sections; and for every $K$-point $x$ of $M.C$ there is a degree-zero divisor equal to $[\,\text{place of }x\,] - [\,\text{place of }s\,]$ whose class is sent by $\mathrm{pts}$ to $x$ followed by $aj$.
--
--   This is the Jacobian of a curve over an algebraically closed field of arbitrary characteristic, packaged in functor-of-points form: an abelian scheme over $K$ together with the Abel–Jacobi morphism from the model and the identification of $\mathrm{Pic}^0(F/K)$ with the $K$-points of the Jacobian, normalised so that the base point $s$ maps to the unit. It is the consumer-facing form used downstream, for instance in the statement that $\mathrm{Pic}^0$ is divisible by the characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_relativeGroupLaw_equiv_of_curveModel.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve

universe u v

theorem AlgebraicCurve.Pic0.exists_relativeGroupLaw_equiv_of_curveModel
    (K : Type u) [Field K] [IsAlgClosed K] (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    ∃ (J : Scheme.{u}) (f : J ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
      (aj : SchemeHomOver M.toBase f)
      (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f),
      AbelianSchemePropertyBundle K f ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
        L.mul t x y = L.mul t y x) ∧
      s.1 ≫ aj.1 = (L.one (𝟙 (Spec (CommRingCat.of K)))).1 ∧
      (∀ x y : Pic0 K F, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of K))) (pts x) (pts y)) ∧
      ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) =
            Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1 := by sorry
