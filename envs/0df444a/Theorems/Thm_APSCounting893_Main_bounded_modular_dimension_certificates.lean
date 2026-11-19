-- Prove2me | Theorems.Thm_APSCounting893_Main_bounded_modular_dimension_certificates
-- name    : APSCounting893.Main.bounded_modular_dimension_certificates
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:46:45.176003+00:00
-- url     : https://prove2.me/theorems/cc3fb8a2-e6b4-4e4e-a1c3-c6123bfcb92c
-- title:
--   Bounded modular certificates characterize rational image dimension
-- statement:
--   Let $C$ be a valid arithmetic circuit over $\mathbb Q$, including circuits with division gates whose outputs are promised polynomials. Let $F_C$ be its polynomial map over $\mathbb C$, and let $Y_C$ be the Zariski closure of its image. Let $\operatorname{Cert}(C,k)$ be the bounded modular Jacobian-certificate predicate defined in the accompanying module. Then there is a natural number $r$ such that
--
--   $$
--   \dim Y_C=r,\qquad k\le r\iff\operatorname{Cert}(C,k)\quad\text{for every }k\ge0.
--   $$
--
--   In this predicate, a certificate consists of distinct output and variable indices, a prime $p$, and a sparse integer point where the cleared Jacobian minor is nonzero modulo $p$. For circuit encoding length $L$, selected variable indices have at most $L$ bits, $p$ has at most $128(L+1)+8$ bits, and the encoded sparse point has length at most $32(L+1)^2$.
--
--   This connects algebraic image dimension with bounded finite arithmetic data. It applies even when the declared number of variables is given in binary and many variables are unused. The empty-output and zero-dimensional cases are included. This theorem supplies the mathematical certificate equivalence; the uniform finite-machine search is a separate theorem.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 6, Lemma 6.1 and proof, p.23. Auxiliary modular implementation of its characteristic-zero Jacobian-rank step; explicit witness bounds are proved here. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf#page=23 . Schwartz–Zippel: Mathlib 0df444a, Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean, schwartz_zippel_totalDegree; modular witness: Mathlib/NumberTheory/Chebyshev.lean, two_pow_le_mul_lcmUpto.

import Definitions.Def_APSCounting893_Main_ModularJacobianData
set_option autoImplicit false

theorem APSCounting893.Main.bounded_modular_dimension_certificates {n : ℕ} (C : APSCounting893.Main.ArithmeticCircuit n)
    (hvalid : APSCounting893.Main.ValidCircuit .rational C) :
    ∃ r : ℕ,RSCapacity.algDim (APSCounting893.Main.imageClosure (APSCounting893.Main.rationalComplexPolynomials C))=
      ((r : ℕ∞) : WithBot ℕ∞) ∧
      ∀ k : ℕ,k≤r ↔ APSCounting893.Main.ModularJacobianCertificate C k := by sorry
