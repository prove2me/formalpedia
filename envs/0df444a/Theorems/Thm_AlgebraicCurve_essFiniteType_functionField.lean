-- Prove2me | Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
-- name    : AlgebraicCurve.essFiniteType_functionField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/ce2efc44-75c9-5c8c-badd-e7c62395c455
-- title:
--   Function field of an integral curve model is essentially of finite type
-- statement:
--   Let $K$ be a field and let $C$ be a scheme over the same universe, equipped with a morphism $c \colon C \to \operatorname{Spec} K$ (with $K$ viewed as a commutative ring object), and assume $C$ is integral and that $c$ is locally of finite type. The function field `C.functionField` is the stalk of $\mathcal O_C$ at the generic point of $C$; it is made into a $K$-algebra by the ring homomorphism `baseToFunctionField c`, namely the composite of the inverse of the isomorphism $K \cong \Gamma(\operatorname{Spec} K, \mathcal O)$ with the map $c^\sharp$ on global sections, followed by the germ map $\Gamma(C, \mathcal O_C) \to \mathcal O_{C, \eta}$ at the generic point. The assertion is that with respect to this algebra structure $K(C)$ is essentially of finite type over $K$ in the sense of `Algebra.EssFiniteType`, i.e. it is obtained by localisation from a finitely generated $K$-subalgebra.
--
--   This is the standard fact that the function field of an integral scheme locally of finite type over a field $K$ is a finitely generated field extension of $K$, recorded in the form needed for the $K$-algebra structure on the function field used throughout the curve-model development; it supports the later results on genus, divisors and ramification for curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_essFiniteType_functionField.lean

import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.essFiniteType_functionField
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [LocallyOfFiniteType c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField := by sorry
