-- Prove2me | Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
-- name    : AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/75d35402-9c3b-5962-860b-ccf669cfd75b
-- title:
--   Principal divisors on the rational function field
-- statement:
--   Let $K$ be a field. The assertion is that the class `HasPrincipalDivisors K (RatFunc K)` holds for the rational function field $K(t)$ over $K$, i.e. that its single field `exists_divisor` is satisfied: for every $f \in K(t)$ with $f \neq 0$ there exists a divisor $D$, that is, a finitely supported function from `Place K (RatFunc K)` to $\mathbb{Z}$, such that (i) $D\,v = v.\mathrm{ord}\,f$ for every place $v$, and (ii) $\mathrm{Divisor.degree}\,D = 0$, where `Divisor.degree` is the additive map sending $D$ to $\sum_v D\,v \cdot v.\mathrm{deg}$, the sum being over the (finite) support of $D$. Here a place of $K(t)$ over $K$ is, by the definition of the structure `Place`, a valuation subring of $K(t)$ which contains the image of $K$ under the structure map, is not the whole of $K(t)$, and is a principal ideal ring; $v.\mathrm{ord}$ and $v.\mathrm{deg}$ are the associated order function and residue degree. Thus the content is twofold: the zeros and poles of a nonzero rational function are finite in number, so that $v \mapsto v.\mathrm{ord}\,f$ is a divisor, and that divisor has degree zero.
--
--   This is the classical degree formula $\sum_v \mathrm{ord}_v(f)\cdot\deg v = 0$ for the genus-zero function field $K(t)$, together with the finiteness of the set of zeros and poles, packaged as the hypothesis class used by the divisor class group development. It is the instance on which the subsequent results about the places of $K(t)$ — among them the computation of degrees over an algebraically closed field and the evaluation maps at the place at infinity and at the places attached to points — rely.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors.lean

import Mathlib.FieldTheory.RatFunc.Basic
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors (K : Type*) [Field K] : HasPrincipalDivisors K (RatFunc K) := by sorry
