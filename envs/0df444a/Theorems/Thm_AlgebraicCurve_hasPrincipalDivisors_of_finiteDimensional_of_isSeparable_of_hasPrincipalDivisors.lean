-- Prove2me | Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
-- name    : AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/16c2f612-a851-5dd7-b7b1-0daa851480b9
-- title:
--   Principal divisors ascend finite separable extensions
-- statement:
--   Let $K$, $F$, $L$ be fields with $F$ and $L$ algebras over $K$ and $L$ an algebra over $F$, the three structures being compatible (a scalar tower), with $L/F$ finite and separable. Here a place of $F$ over $K$ is a valuation subring of $F$ containing the image of $K$, different from all of $F$, and whose ideals are principal; a divisor is a finitely supported $\mathbb{Z}$-valued function on the set of such places, and its degree is $\sum_v D(v)\,\deg v$. The hypothesis `HasPrincipalDivisors K F` says that for every nonzero $f\in F$ there is a divisor $D$ of $F$ over $K$ with $D(v)=\operatorname{ord}_v f$ at every place $v$ of $F$ over $K$ and $\deg D = 0$; in particular the function $v\mapsto\operatorname{ord}_v f$ has finite support and total degree zero. The conclusion is the same property for $L$ over $K$: for every nonzero $g\in L$ there is a divisor of $L$ over $K$ whose value at each place $w$ of $L$ over $K$ is $\operatorname{ord}_w g$, and whose degree is $0$.
--
--   This is the statement that the degree-zero property of divisors of functions passes from a function field to any finite separable extension of it, with no hypothesis on the characteristic or on the constant field $K$ beyond the tower structure. It is used to produce function fields with principal divisors from given ones, for instance Kummer extensions arising in the treatment of the Weil pairing and in the comparison of genera.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_DivisorPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable_of_hasPrincipalDivisors
    (K F L : Type*) [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [HasPrincipalDivisors K F] :
    HasPrincipalDivisors K L := by sorry
