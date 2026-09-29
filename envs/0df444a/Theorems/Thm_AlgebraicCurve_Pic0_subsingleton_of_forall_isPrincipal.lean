-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal
-- name    : AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/cbb2dd71-fe1d-5b0a-a5ca-054b1785ae39
-- title:
--   Principality of all degree-zero divisors makes Pic⁰ trivial
-- statement:
--   Let $K$ and $F$ be fields with $F$ an algebra over $K$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$ under the structure map, is not all of $F$, and is a principal ideal ring; a divisor is a finitely supported function from places to $\mathbb{Z}$, its degree is the sum $\sum_v D(v)\cdot \deg v$ over the support, where $\deg v$ is the residue-degree invariant `Place.deg` attached to $v$, and a divisor $D$ is principal when there is a nonzero $f \in F$ with $D(v) = \mathrm{ord}_v(f)$ for every place $v$, where $\mathrm{ord}_v$ is the order function `Place.ord` of $v$. The hypothesis is that every divisor $D$ of $F/K$ with $\mathrm{degree}(D) = 0$ is principal. The conclusion is that `Pic0 K F`, the quotient of the kernel of the degree homomorphism by the subgroup of principal divisors of degree zero, is a subsingleton, i.e. any two of its elements are equal.
--
--   This is the standard criterion for vanishing of the degree-zero divisor class group of a function field: $\mathrm{Pic}^0$ is trivial exactly when all degree-zero divisors are principal. It is used in the project to deduce triviality of $\mathrm{Pic}^0$ in the genus-zero case and, through that, in the comparison of specialisation maps on $\mathrm{Pic}^0$ with reduction modulo $\ell$ for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_subsingleton_of_forall_isPrincipal.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.subsingleton_of_forall_isPrincipal (K F : Type*) [Field K] [Field F] [Algebra K F]
    (h : ∀ D : Divisor K F, Divisor.degree D = 0 → D.IsPrincipal) :
    Subsingleton (Pic0 K F) := by sorry
