-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_partial_space_finite_dimensional
-- name    : DerivationHitting.Commutative.partial_space_finite_dimensional
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:23.249902+00:00
-- url     : https://prove2.me/theorems/aa28128a-5891-4662-96ca-4823714e24ec
-- title:
--   §1 — Finiteness of the ordinary derivative space
-- statement:
--   Let $F$ be a characteristic-zero field, let $n\in\mathbb N$, and let $f\in F[x_1,\ldots,x_n]$. Write $V_f$ for the span of all ordinary iterated partial derivatives of $f$, including $f$ itself. Then
--   $$
--    V_f\subseteq F[x_1,\ldots,x_n]_{\le\deg f},\qquad \dim_F V_f<\infty.
--   $$
--   Here the right-hand space consists of polynomials of total degree at most that of $f$, with degree zero assigned to the zero polynomial for this upper bound. This is an unnumbered background fact underlying the paper's derivative-space dimension, included to make finiteness an explicit supporting obligation. It is not a new numbered milestone.
--
--   Differences from the source:
--   - encoding: variables indexed by 1,…,n → variables indexed by Fin n, with integer parameter i.val+1; reason: this is a bijective reindexing and the first kernel is nonzero
--   - encoding: dimension of the span of all ordinary partial derivatives → cardinal Module.rank of the span of derivatives indexed by all finite sequences, including the empty sequence; reason: finite-dimensional cardinal rank is ordinary dimension, and no finrank default is used
--   - encoding: all derivatives have degree at most the input degree → containment in Mathlib restrictTotalDegree, with totalDegree 0 = 0; reason: the zero polynomial belongs to this subspace and no nonzero instance changes
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026), p. 3, §1, discussion of the space of all partial derivatives before Theorem 1.1; unnumbered background fact; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/577.pdf

import Definitions.Def_DerivationHitting_Commutative_PolynomialData

namespace DerivationHitting.Commutative
theorem partial_space_finite_dimensional {F : Type*} [Field F] [CharZero F] {n : ℕ}
    (f : MvPolynomial (Fin n) F) :
    partialSpace f ≤ MvPolynomial.restrictTotalDegree (Fin n) F f.totalDegree ∧
      FiniteDimensional F (partialSpace f) := by sorry
end DerivationHitting.Commutative
