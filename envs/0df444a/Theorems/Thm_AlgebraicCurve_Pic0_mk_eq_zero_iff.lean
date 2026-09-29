-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff
-- name    : AlgebraicCurve.Pic0.mk_eq_zero_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/e5aababf-e83b-5e51-80f1-1b615c3a646e
-- title:
--   A class in Pic⁰ vanishes iff the divisor is principal
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, its degree is the sum of its values weighted by the residue degrees $v.\mathrm{deg}$, and `Divisor.degZero` is the kernel of the degree homomorphism. A divisor $D$ satisfies `Divisor.IsPrincipal` when there is $f \in F$, $f \neq 0$, with $D v = v.\mathrm{ord}\, f$ for every place $v$; such divisors form the subgroup `Divisor.principal`. The group $\mathrm{Pic}^0$ is the quotient of `Divisor.degZero` by the intersection of `Divisor.principal` with it. The theorem asserts, for every element $D$ of `Divisor.degZero`, that the class `Pic0.mk D` is zero in this quotient if and only if the underlying divisor of $D$ is principal in the above sense.
--
--   This is the basic identification of the kernel of the map from degree-zero divisors to the degree-zero divisor class group, and is the entry point for every argument showing that a particular class in $\mathrm{Pic}^0$ does or does not vanish. It is used, among other places, in the injectivity criteria for the divisorial Weil pairing and in the statement that a class killed by an integer has a suitable principal multiple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_mk_eq_zero_iff.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.mk_eq_zero_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) : Pic0.mk D = 0 ↔ Divisor.IsPrincipal (D : Divisor K F) := by sorry
