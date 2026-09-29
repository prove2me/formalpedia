-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_factorial_denominator_obstruction
-- name    : EulerMascheroni.Arithmetic.factorial_denominator_obstruction
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T13:19:33.107125+00:00
-- url     : https://prove2.me/theorems/d45b27ea-09bc-41ed-a023-0683ce357da6
-- title:
--   G-function obstruction to exponential denominators for the factorial quotient
-- statement:
--   For an algebraic real number $a$, put
--
--   $$q_n(a)=\frac{a-\sum_{k=0}^{n-1}(-1)^k k!}{n!}.$$
--
--   There is no real $C\ge1$ such that, for every $n\ge0$, a positive integer $D_n\le C^{n+1}$ makes all $D_nq_k(a)$, $0\le k\le n$, algebraic integers:
--
--   $$\neg\exists C\ge1\;\forall n\;\exists D_n\in\mathbb N_{>0}:\ D_n\le C^{n+1}\ \text{and}\ D_nq_k(a)\in\overline{\mathbb Z}\ (k\le n).$$
--
--   This is an unconditional corollary of classical G-function differential-equation theory, formulated here as a concrete arithmetic formalization task. It is not a claimed existing Lean result.
-- source:
--   Explicit corollary of the André–Chudnovsky–Katz theorem as stated in Fischler–Rivoal, Linear independence of values of G-functions, II, https://www.imo.universite-paris-saclay.fr/~stephane.fischler/pade_fns.pdf, PDF pp. 4–5, definition of G-functions and minimal G-operators. Derivation for this sequence: C_a(z)=sum q_n(a)z^n satisfies C_a'-C_a=-1/(1+z), hence (1+z)C_a''-zC_a'-C_a=0. A rational solution is excluded by pole orders. A first-order homogeneous equation would force C_a rational, so this order-two operator is minimal. It is irregular at infinity, contrary to the cited theorem if exponential denominator bounds held. Conjugate growth bounds follow from the explicit factorial formula.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.factorial_denominator_obstruction
    (a : ℝ) (ha : IsAlgebraic ℚ a) :
    ¬ EulerMascheroni.Arithmetic.ExponentialDenominators a := by sorry
