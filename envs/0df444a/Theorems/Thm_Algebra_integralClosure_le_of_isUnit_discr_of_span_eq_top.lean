-- Prove2me | Theorems.Thm_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top
-- name    : Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/c406bcd6-5742-592f-a0e6-7a1fc4de61aa
-- title:
--   Unit discriminant forces S to contain the integral closure
-- statement:
--   Let $R$ be a commutative integral domain which is integrally closed, with $K$ a field that is a fraction field of $R$ via the given $R$-algebra structure. Let $A$ be a commutative ring which is simultaneously a $K$-algebra and an $R$-algebra, compatibly ($R \to K \to A$ a scalar tower), and assume $A$ is finite-dimensional over $K$. Let $S$ be an $R$-subalgebra of $A$ whose underlying set spans $A$ as a $K$-vector space, i.e. $\operatorname{span}_K(S) = \top$. Suppose $S$ is free as an $R$-module with a basis $b$ indexed by a finite type $\iota$ with decidable equality, and suppose the discriminant $\operatorname{discr}_R(b) = \det\bigl(\operatorname{Tr}_{S/R}(b_i b_j)\bigr)_{i,j}$ is a unit of $R$. Then the integral closure of $R$ in $A$ is contained in $S$: every element of $A$ integral over $R$ already lies in $S$. (Combined with the integrality of the elements of $S$ over $R$, this identifies $S$ with the maximal $R$-order in $A$, though only the stated inclusion is asserted.)
--
--   This is the standard criterion that an order of unit discriminant is maximal (as in Neukirch, Ch. I, (2.9)–(2.10)), here in the relative setting of an integrally closed base domain $R$ and a finite-dimensional commutative algebra $A$ over its fraction field. It is used in the construction of regular prolongations on algebraic curves, where a subalgebra spanning the generic fibre and having unit discriminant is shown to capture all integral elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_integralClosure_le_of_isUnit_discr_of_span_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K A]
    (S : Subalgebra R A) (hS : Submodule.span K ((S : Subalgebra R A) : Set A) = ⊤)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (hdisc : IsUnit (Algebra.discr R b)) :
    integralClosure R A ≤ S := by sorry
