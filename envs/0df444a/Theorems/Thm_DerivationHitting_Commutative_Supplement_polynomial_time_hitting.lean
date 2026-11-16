-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_Supplement_polynomial_time_hitting
-- name    : DerivationHitting.Commutative.Supplement.polynomial_time_hitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:30.435391+00:00
-- url     : https://prove2.me/theorems/61177ae7-acd1-47cd-aeda-115c1b42bff3
-- title:
--   Theorem 1.2 — Polynomial-time rational hitting point
-- statement:
--   There is one deterministic finite-alphabet Turing machine and one polynomial time bound that, on unary input n,s, writes the explicitly encoded rational matrix tuple of dimension B=ns²+s. Entries are signed integer numerator and positive denominator pairs in binary; the actual bounded-loop emitter is fixed by the definition, without dependence on F or f. All internal alphabets are finite, and runtime is measured in Turing-machine steps against input length n+s+1.
--
--   For every characteristic-zero field F and every nonzero noncommutative polynomial f in n letters computed by a homogeneous ncABP of at most s vertices, casting these same rational matrices into F gives
--
--   $$\dim\widetilde T_i=B\le ns^2+s,\qquad f(\widetilde T_1,\ldots,\widetilde T_n)\ne0.$$
--
--   The matrices have entries (−1)^{r−k−1}i^{r−k}/r below the diagonal and zero elsewhere. Their rationality, uniformity, dimension and bit-polynomial construction are part of this single result. No field coefficients are supplied to the algorithm. When s=0 there is no eligible ABP; when n=0 only scalar polynomials are possible. This companion theorem adds computational content to Theorem 5.12 and is not used by the published commutative goal.
--
--   Differences from the source:
--   - encoding: variables numbered 1,…,n → variables Fin n with source index i.val+1; reason: a bijective change of indices preserves every coefficient
--   - encoding: finite linear combinations of noncommutative words and ordered path weights → the monoid algebra of the free monoid, with adjacency-power path sums; reason: convolution concatenates words and strictly forward edges bound all paths by m−1 for m vertices
--   - encoding: the explicit matrices obtained by truncating the integration operators → the displayed coefficient formulas on column-vector bases; reason: row r is the coefficient of t^r in the image of t^k, with no change of matrix product order
--   - encoding: one polynomial-time algorithm on unary n,s outputs rational matrices → a finite-alphabet TM2 computes the executable binary signed numerator/positive denominator emitter with one polynomial clock; reason: finite alphabets on every stack ensure bit computation; the machine and polynomial precede n,s,F,f and are uniform
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. p.5, Theorem 1.2; p.21, its explicit matrix realization.

import Definitions.Def_DerivationHitting_Commutative_Supplement_AlgorithmData

namespace DerivationHitting.Commutative.Supplement

theorem polynomial_time_hitting :
    (∃ M : Turing.TM2ComputableInPolyTime unaryInput
        (id : List OutputSymbol → List OutputSymbol) rationalMatrixOutput,
      ∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
    ∀ n s : ℕ, cutoff n s ≤ n * s ^ 2 + s ∧
      ∀ (F : Type*) [Field F] [CharZero F] (f : NCPoly F n),
        f ≠ 0 → ComputableByHomogeneousABP f s →
          matrixEvaluation (sectionMatrices (F := F) n s) f ≠ 0 := by sorry

end DerivationHitting.Commutative.Supplement
