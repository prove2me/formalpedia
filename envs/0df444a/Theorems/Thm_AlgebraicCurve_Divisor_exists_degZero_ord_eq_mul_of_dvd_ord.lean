-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
-- name    : AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/d0cbc845-0028-5fbc-a99d-35fd62e92e8c
-- title:
--   Division of a principal divisor by n
-- statement:
--   Let $K \subseteq F$ be fields with $F$ a $K$-algebra, and let $n$ be a natural number with $n \neq 0$. A place of $F$ over $K$, in the sense used here, is a valuation subring of $F$ which contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; for such a place $v$ and $f \in F$, $\mathrm{ord}_v(f)$ is minus the logarithm of the value of $f$ under the $\mathbb{Z}^{m0}$-valued valuation attached to the height-one prime of $v$. A divisor is a finitely supported function from places to $\mathbb{Z}$, its degree is $\sum_v D(v)\,\deg(v)$, and the degree-zero divisors form the kernel of this homomorphism. Assume that $F/K$ satisfies `HasPrincipalDivisors`, i.e. every nonzero $g \in F$ admits a divisor $D$ with $D(v) = \mathrm{ord}_v(g)$ at every place $v$ and $\deg D = 0$. Then for every nonzero $f \in F$ such that $n \mid \mathrm{ord}_v(f)$ in $\mathbb{Z}$ for all places $v$, there exists a degree-zero divisor $D$ with $\mathrm{ord}_v(f) = n \cdot D(v)$ for every place $v$.
--
--   This is the elementary step underlying the Kummer-theoretic description of $n$-torsion in the divisor class group: a function whose order is divisible by $n$ at every place has $\tfrac1n\,\mathrm{div}(f)$ again a degree-zero divisor. It is used in the identification of the image of $\mathrm{Pic}^0$ in [`AlgebraicCurve.Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff`](thm.html#AlgebraicCurve.Pic0.range_eq_setOf_cartier_fixed_and_isRegularDiff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.exists_degZero_ord_eq_mul_of_dvd_ord {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (hn : n ≠ 0) [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0)
    (hdvd : ∀ v : Place K F, (n : ℤ) ∣ v.ord f) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by sorry
