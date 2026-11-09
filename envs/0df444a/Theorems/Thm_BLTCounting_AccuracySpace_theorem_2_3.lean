-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_theorem_2_3
-- name    : BLTCounting.AccuracySpace.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:14.234894+00:00
-- url     : https://prove2.me/theorems/e73711c9-9cf4-4e2b-81f5-1b3f2da8c471
-- title:
--   Eckart–Young–Mirsky for complex matrices
-- statement:
--   Let $A$ and $X$ be complex matrices of the same shape, with $\mathrm{rank}\,X\le d$. Then
--   $$s_{d+1}(A)\le\|A-X\|_2.$$
--   Consequently, if also $\|A-X\|_2\le\tau$, then $d\ge\#\{j:s_j(A)>\tau\}$.
--
--   This converts a low-rank approximation into a bound on the number of large singular values.
--
--   Differences from the source:
--   - encoding: $s_{d+1}(A)$, defined for $d+1\le\min(m,n)$ → the zero-indexed, zero-extended `singularValue A d`; reason: for $d\ge\min(m,n)$ the value is $0$ and the inequality is the trivial one; no instance of the source is lost
--   - generalization: complex matrices with positive row and column dimensions → arbitrary finite row and column index types, including empty ones; reason: if either dimension is zero, the matrices, operator norm and singular-value count are zero; all positive-dimensional source instances are retained
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Theorem 2.3, printed p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_MatrixNorms

open Matrix

namespace BLTCounting.AccuracySpace

/-- Theorem 2.3 (Eckart–Young–Mirsky), PDF p. 11: for complex matrices `A`, `X` of the same shape with
`rank(X) ≤ d`, one has `s_{d+1}(A) ≤ ‖A - X‖₂` (`singularValue` is zero-indexed), and if moreover
`‖A - X‖₂ ≤ τ` then `d ≥ #{j : s_j(A) > τ}`. -/
theorem theorem_2_3 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A X : Matrix m n ℂ) (d : ℕ) (hX : X.rank ≤ d) :
    singularValue A d ≤ specNorm (A - X) ∧
      ∀ τ : ℝ, specNorm (A - X) ≤ τ → singularCountAbove A τ ≤ d := by sorry

end BLTCounting.AccuracySpace
