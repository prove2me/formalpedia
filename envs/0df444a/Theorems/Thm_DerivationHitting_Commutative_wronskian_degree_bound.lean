-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_wronskian_degree_bound
-- name    : DerivationHitting.Commutative.wronskian_degree_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:59.743833+00:00
-- url     : https://prove2.me/theorems/5534db8a-5e0a-4ae2-a71d-468a67651801
-- title:
--   Corollary 3.5 — Numerator and denominator degree bounds
-- statement:
--   Let $F$ be a characteristic-zero field, let $n,q\in\mathbb N$, and let $g_1,\ldots,g_q\in F[x_1,\ldots,x_n]$ have derivative-closed $F$-linear span. For $D=\partial_t+\sum_{i=1}^n\frac{i}{1+it}\partial_{x_i}$, there are polynomials $A,C\in F[t]$ such that
--   $$
--    C\ne0,\qquad \deg A\le nq^2,\qquad \deg C\le nq^2,\qquad
--    W_D(g_1,\ldots,g_q)=\frac{A(t)}{C(t)}.
--   $$
--   The equality is in $F(t)[x_1,\ldots,x_n]$, with the fraction embedded as an $x$-constant polynomial. The denominator is named $C$ to distinguish it from the natural cutoff $B=nr^2+r$. No nonzero determinant assumption is needed. This is the quantitative rational-function bound used by Theorem 4.1.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - generalization: a degree-ordered basis of a derivative space, with the section normalizations → any finite family of t-free polynomials whose F-linear span is derivative-closed; reason: every source basis is such a family; changing the basis changes the Wronskian by a constant determinant, while a dependent family has zero Wronskian
--   - encoding: a rational fraction A(t)/B(t) with degrees at most nr² → a nonzero polynomial denominator C and natDegree bounds at most nq²; reason: renaming the family size and denominator changes no instances; zero numerator has natDegree zero
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 14, Corollary 3.5 and §3 standing basis setup; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_DifferentialData

namespace DerivationHitting.Commutative
theorem wronskian_degree_bound {F : Type*} [Field F] [CharZero F] {n q : ℕ}
    (g : Fin q → MvPolynomial (Fin n) F) (hclosed : derivativeClosed g) :
    ∃ A C : Polynomial F, C ≠ 0 ∧ A.natDegree ≤ n * q ^ 2 ∧
      C.natDegree ≤ n * q ^ 2 ∧
      derivationWronskian logarithmKernel g =
        MvPolynomial.C (algebraMap (Polynomial F) (RatFunc F) A /
          algebraMap (Polynomial F) (RatFunc F) C) := by sorry
end DerivationHitting.Commutative
