-- Prove2me | Theorems.Thm_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero
-- name    : AlgebraicCurve.algHom_eq_of_forall_restrictAlong_eq_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/975ad7de-6d5f-5b2e-a819-d208991b6886
-- title:
--   Rigidity of curve embeddings agreeing on all places
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$, and let $F_0$ and $F_1$ be fields equipped with $K$-algebra structures, each essentially of finite type over $K$ and each a curve over $K$ in the sense of the class `IsCurveOver`: every nonzero element $f$ admits a divisor of degree $0$ whose value at each place equals $v.\mathrm{ord}\,f$, every place of the field over $K$ has residue field of finite $K$-dimension, and the module of Kähler differentials over $K$ is free of rank one over the field. Here a place of a field $F$ over $K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring. Let $\varphi_1,\varphi_2 : F_0 \to F_1$ be $K$-algebra homomorphisms whose underlying ring homomorphisms are integral, and suppose that for every place $w$ of $F_1$ over $K$ the two restrictions agree, i.e. the preimages of the valuation subring of $w$ under $\varphi_1$ and under $\varphi_2$ coincide as places of $F_0$ over $K$. Then $\varphi_1 = \varphi_2$.
--
--   This is the rigidity statement that two finite (integral) embeddings of one-variable function fields over an algebraically closed base field inducing the same map on places must coincide — geometrically, two dominant morphisms of smooth proper curves that agree on closed points are equal; classically this holds in every characteristic, whereas the statement here assumes $\operatorname{char} K = 0$. It is used in [`CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.ModuliTowerWitness.tower_laws_of_two_mul_dvd) to identify maps in a tower of moduli curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_algHom_eq_of_forall_restrictAlong_eq_of_charZero.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.algHom_eq_of_forall_restrictAlong_eq_of_charZero
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (F₀ F₁ : Type) [Field F₀] [Field F₁] [Algebra K F₀] [Algebra K F₁]
    [IsCurveOver K F₀] [Algebra.EssFiniteType K F₀] [IsCurveOver K F₁] [Algebra.EssFiniteType K F₁]
    (φ₁ φ₂ : F₀ →ₐ[K] F₁) (h₁ : φ₁.IsIntegral) (h₂ : φ₂.IsIntegral)
    (h : ∀ w : Place K F₁, w.restrictAlong φ₁ h₁ = w.restrictAlong φ₂ h₂) :
    φ₁ = φ₂ := by sorry
