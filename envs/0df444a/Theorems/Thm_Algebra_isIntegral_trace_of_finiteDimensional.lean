-- Prove2me | Theorems.Thm_Algebra_isIntegral_trace_of_finiteDimensional
-- name    : Algebra.isIntegral_trace_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/912cdb85-7254-509b-8341-c68687ba2f99
-- title:
--   Trace of an integral element is integral
-- statement:
--   Let $R$ be a commutative ring, $K$ a field equipped with an $R$-algebra structure, and $A$ a commutative ring that is both a $K$-algebra and an $R$-algebra, the two structures being compatible in the sense that $R \to K \to A$ is a scalar tower, and assume $A$ is finite-dimensional as a $K$-vector space. Let $x \in A$ be integral over $R$, i.e. annihilated by some monic polynomial with coefficients in $R$ (more precisely, by the image of such a polynomial under the structure map). Then the algebra trace $\operatorname{Tr}_{A/K}(x) \in K$, the trace of the $K$-linear endomorphism of $A$ given by multiplication by $x$, is again integral over $R$. Note that $A$ is only required to be a finite-dimensional commutative $K$-algebra: it need not be reduced, nor a field, so the statement is more general than the form in which only field extensions $A/K$ are allowed.
--
--   This is the classical assertion that the trace form transports integrality, the first step towards 'the trace of an algebraic integer is an algebraic integer' and, with $R$ integrally closed in $K$, towards $\operatorname{Tr}_{A/K}(x) \in R$. It is used here in the study of the discriminant of a finite algebra, namely by [`Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top`](thm.html#Algebra.integralClosure_le_of_isUnit_discr_of_span_eq_top).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isIntegral_trace_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Algebra.isIntegral_trace_of_finiteDimensional
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K A]
    {x : A} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace K A x) := by sorry
