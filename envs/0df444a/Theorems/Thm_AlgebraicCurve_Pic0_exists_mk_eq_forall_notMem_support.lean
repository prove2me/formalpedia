-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support
-- name    : AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/1bcf08c0-c390-57ab-9a08-b2f4f15efd4d
-- title:
--   Moving lemma for degree-zero divisor classes
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let `Place K F` be the type of places of $F/K$, a place being a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring. Divisors are the finitely supported functions `Place K F →₀ ℤ`, the degree homomorphism sends $D$ to $\sum_v D(v)\cdot \deg v$, and `Divisor.degZero` is its kernel; `Divisor.principal` is the subgroup of divisors $D$ for which there is some $f \neq 0$ in $F$ with $D(v) = \operatorname{ord}_v f$ at every place $v$, and $\mathrm{Pic}^0$ is the quotient of the degree-zero divisors by the intersection of `Divisor.principal` with them. Assume `HasPrincipalDivisors K F`, i.e. every nonzero $f \in F$ admits a (finitely supported) divisor $D$ with $D(v) = \operatorname{ord}_v f$ for all places $v$ and $\deg D = 0$. Then for every class $x \in \mathrm{Pic}^0(K,F)$ and every finite set $S$ of places there exists a degree-zero divisor $D$ whose class is $x$ and such that no place in the support of $D$ belongs to $S$.
--
--   This is the moving lemma for divisor classes: a degree-zero class may be represented by a divisor whose support avoids any prescribed finite set of places. It is used in the comparison of $\mathrm{Pic}^0$ with glued Picard data ([`AlgebraicCurve.GluedPic0.toPic0Pair_surjective`](thm.html#AlgebraicCurve.GluedPic0.toPic0Pair_surjective) and the associated torsion statements) and in the moving lemma for torsion classes with rational support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F), Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S := by sorry
