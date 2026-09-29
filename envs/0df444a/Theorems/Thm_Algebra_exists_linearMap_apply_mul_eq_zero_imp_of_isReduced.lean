-- Prove2me | Theorems.Thm_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
-- name    : Algebra.exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/349a85c1-75fb-5339-b4e5-55b82e1a8e34
-- title:
--   Reduced finite-dimensional algebras carry a nondegenerate trace form
-- statement:
--   Let $K$ be a field and $A$ a commutative ring equipped with a $K$-algebra structure, such that $A$ is finite-dimensional as a $K$-vector space and reduced (its only nilpotent element is $0$). The assertion is that there exists a $K$-linear map $l : A \to K$ with the following property: for every $x \in A$, if $l(x y) = 0$ for all $y \in A$, then $x = 0$. Thus the symmetric $K$-bilinear form $(x,y) \mapsto l(xy)$ on $A$ has trivial left kernel; by symmetry of multiplication this is exactly nondegeneracy of that form, i.e. $A$ is a Frobenius algebra over $K$ with Frobenius functional $l$. Only existence of such a functional is claimed; no canonical choice (for instance the trace of the regular representation) is made, and no statement is made about the induced isomorphism $A \cong \operatorname{Hom}_K(A,K)$ of $A$-modules.
--
--   This is the standard fact that a finite-dimensional reduced commutative algebra over a field is a (symmetric) Frobenius algebra. It is used in the bound [`Ideal.exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced`](thm.html#Ideal.exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced), which compares, uniformly in $m$, the index of the $m$-th power of a finite-index ideal in a reduced order with the number of corresponding torsion points, a step towards controlling the Gorenstein defect of reduced Hecke orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] :
    ∃ l : A →ₗ[K] K, ∀ x : A, (∀ y : A, l (x * y) = 0) → x = 0 := by sorry
