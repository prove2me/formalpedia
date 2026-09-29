-- Prove2me | Theorems.Thm_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow
-- name    : Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/42e97b56-99f6-5caa-a6a7-8da33dadc83d
-- title:
--   Norm of c-x as a power of minpoly(x) at c
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is finite-dimensional over $K$, let $x \in L$ and let $c \in K$. Write $p = \mathrm{minpoly}_K(x) \in K[X]$ for the minimal polynomial of $x$ over $K$. The assertion is the identity
--   $$N_{L/K}\bigl(c\cdot 1_L - x\bigr) = p(c)^{\,\lfloor [L:K]/\deg p\rfloor},$$
--   where $c \cdot 1_L$ denotes the image of $c$ under the structure map $K \to L$, $N_{L/K}$ is the algebra norm (the determinant of multiplication by the element, viewed as a $K$-linear endomorphism of $L$), $[L:K]$ is the $K$-rank of $L$, and the exponent is the natural-number quotient of $[L:K]$ by the natural degree of $p$. Since $\deg p = [K(x):K]$ divides $[L:K]$, this truncated division is exact and the exponent equals $[L:K(x)]$. No separability or normality hypothesis is imposed, and the value $p(c)$ lies in $K$, so both sides are elements of $K$.
--
--   This is the standard computation of the norm of $c - x$ in a finite field extension: the characteristic polynomial of $x$ over $K$ is $p^{[L:K(x)]}$, evaluated at $c$ up to sign. It is used in the project's treatment of places of algebraic curves, in the criteria [`AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne`](thm.html#AlgebraicCurve.Place.derivative_evalEval_evalAt_ne_zero_of_ord_sub_eq_one_of_forall_evalAt_ne) and its separable variant, where the nonvanishing of such a norm detects nonvanishing of a derivative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_norm_algebraMap_sub_eq_eval_minpoly_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Algebra.norm_algebraMap_sub_eq_eval_minpoly_pow
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) (c : K) :
    Algebra.norm K (algebraMap K L c - x)
      = ((minpoly K x).eval c) ^ (Module.finrank K L / (minpoly K x).natDegree) := by sorry
