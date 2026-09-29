-- Prove2me | Theorems.Thm_AlgebraicCurve_finiteAlong_of_isIntegral
-- name    : AlgebraicCurve.finiteAlong_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c3a5dfa4-dd68-56a7-9135-0f45b13567df
-- title:
--   Integral maps into essentially finite type fields are finite
-- statement:
--   Let $K$, $F$, $F'$ be fields, with $F$ and $F'$ both $K$-algebras, and assume $F'$ is essentially of finite type over $K$ (`Algebra.EssFiniteType K F'`). Let $\varphi : F \to F'$ be a homomorphism of $K$-algebras whose underlying ring homomorphism is integral, i.e. every element of $F'$ satisfies a monic polynomial with coefficients in the image of $\varphi$. The conclusion is `FiniteAlong K φ`: equipping $F'$ with the $F$-algebra structure induced by $\varphi$ (the algebra structure `algebraAlong φ` coming from $\varphi$ viewed as a ring homomorphism), $F'$ is a finite $F$-module, that is, $[F' : \varphi(F)] < \infty$. No hypothesis of characteristic, separability, perfectness, or of being a one-variable function field is imposed; the statement is one of pure commutative algebra, phrased for an explicit homomorphism $\varphi$ rather than for a field extension.
--
--   This is the algebraic form of the statement that a dominant morphism of curves is finite: for function fields of curves over $K$, an integral $K$-embedding $\varphi$ makes $F'$ a finite extension of $\varphi(F)$. It supplies the finiteness input `FiniteAlong` used in the correspondence formalism, and is invoked in the construction of Čerednik–Drinfel'd moduli towers and in the uniformised Hecke curve for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finiteAlong_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.finiteAlong_of_isIntegral
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra.EssFiniteType K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    FiniteAlong K φ := by sorry
