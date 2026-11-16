-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_Supplement_appendix_matrix_hitting
-- name    : DerivationHitting.Commutative.Supplement.appendix_matrix_hitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:59:00.654897+00:00
-- url     : https://prove2.me/theorems/c8b7d8db-60ab-402f-8f53-4aeb837bf8ba
-- title:
--   Theorem A.6 — Exact appendix matrices for general ncABPs
-- statement:
--   Let F be any characteristic-zero field, let n,s be nonnegative integers, and set N=(s−1)+binom(s,2)(n−1) using natural predecessors, and d=N+1. For each letter numbered i=1,…,n define the d×d matrix
--
--   $$T'_i(r,k)=\begin{cases}i^{r-k}/r&0\le k<r\le N,\\0&\text{otherwise.}\end{cases}$$
--
--   For every nonzero noncommutative polynomial f over F computed by a general ncABP with at most s vertices,
--
--   $$f(T'_1,\ldots,T'_n)\ne0.$$
--
--   Affine labels, nonhomogeneous polynomials and constants are retained. There is no homogenization, size inflation, factor-two slack or additional linear-representation hypothesis. These are the actual matrices (A.5) for i/(1−it). At n=0 evaluation of the empty tuple is scalar evaluation in positive dimension; at s=0 no ABP exists; at s=1, d=1 and only the empty-path polynomial is possible. This is a companion theorem independent of the published goal.
--
--   Differences from the source:
--   - encoding: variables numbered 1,…,n → variables Fin n with source index i.val+1; reason: a bijective change of indices preserves every coefficient
--   - encoding: finite linear combinations of noncommutative words and ordered path weights → the monoid algebra of the free monoid, with adjacency-power path sums; reason: convolution concatenates words and strictly forward edges bound all paths by m−1 for m vertices
--   - encoding: N=s−1+binom(s,2)(n−1) and dimension N+1 → natural predecessors extend the same formula to n=0 or s=0; reason: positive parameters give exactly the printed integer; the empty tuple handles n=0 and there is no zero-vertex ABP
--   - encoding: the appendix integration matrices T′ in equation (A.5) → the entries i^(r−k)/r at k<r<N+1 and zero otherwise; reason: this is the exact column-vector matrix for the source kernel i/(1−it), with no alternating sign
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.26–29, Theorem A.6 and equation (A.5).

import Definitions.Def_DerivationHitting_Commutative_Supplement_MatrixData

namespace DerivationHitting.Commutative.Supplement

theorem appendix_matrix_hitting {F : Type*} [Field F] [CharZero F] (n s : ℕ) :
    ∀ f : NCPoly F n, f ≠ 0 → ComputableByABP f s →
      matrixEvaluation (appendixMatrices (F := F) n s) f ≠ 0 := by sorry

end DerivationHitting.Commutative.Supplement
