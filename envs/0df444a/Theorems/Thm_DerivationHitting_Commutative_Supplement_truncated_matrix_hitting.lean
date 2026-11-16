-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_Supplement_truncated_matrix_hitting
-- name    : DerivationHitting.Commutative.Supplement.truncated_matrix_hitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:58:17.54257+00:00
-- url     : https://prove2.me/theorems/703d929d-c49d-455e-888f-6d9d6ecce623
-- title:
--   Theorem 5.12 — Explicit truncated-integration hitting matrices
-- statement:
--   Let F be any characteristic-zero field and let n,s be nonnegative integers. Fix B=ns²+s and define, for i=1,…,n and 0≤r,k<B,
--
--   $$\widetilde T_i(r,k)=\begin{cases}(-1)^{r-k-1}i^{r-k}/r&k<r,\\0&k\ge r.\end{cases}$$
--
--   For every nonzero noncommutative polynomial f over F computed by a homogeneous ncABP with at most s vertices,
--
--   $$f(\widetilde T_1,\ldots,\widetilde T_n)\ne0.$$
--
--   The tuple is fixed solely by n,s and rational coefficients cast into F. Its dimension is exactly B; it is the matrix on the basis 1,t,…,t^{B−1} of the truncated integration operators for i/(1+it). Evaluation uses ordered products and scalar identity matrices for constants. The statement includes n=0 and s=0. This companion theorem is supported by Lemma 5.11; it does not replace the bit-complexity assertion of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: variables numbered 1,…,n → variables Fin n with source index i.val+1; reason: a bijective change of indices preserves every coefficient
--   - encoding: finite linear combinations of noncommutative words and ordered path weights → the monoid algebra of the free monoid, with adjacency-power path sums; reason: convolution concatenates words and strictly forward edges bound all paths by m−1 for m vertices
--   - encoding: the explicit matrices obtained by truncating the integration operators → the displayed coefficient formulas on column-vector bases; reason: row r is the coefficient of t^r in the image of t^k, with no change of matrix product order
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. p.21, Theorem 5.12.

import Definitions.Def_DerivationHitting_Commutative_Supplement_MatrixData

namespace DerivationHitting.Commutative.Supplement

theorem truncated_matrix_hitting {F : Type*} [Field F] [CharZero F] (n s : ℕ) :
    ∀ f : NCPoly F n, f ≠ 0 → ComputableByHomogeneousABP f s →
      matrixEvaluation (sectionMatrices (F := F) n s) f ≠ 0 := by sorry

end DerivationHitting.Commutative.Supplement
