-- Prove2me | Theorems.Thm_FasterPrimeEnum_lemma_9_11
-- name    : FasterPrimeEnum.lemma_9_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:38:40.262735+00:00
-- url     : https://prove2.me/theorems/bde33a41-2274-474f-9002-d908e23acccf
-- title:
--   Lemma 9.11 — few square-primes below $N$ are not square-$Y$-rough
-- statement:
--   Let $N$ and $Y\le N$ be positive integers. Then at most
--
--   $$
--   O\big(N^{1/2}Y^{1/2}\big)
--   $$
--
--   positive integers $n<N$ are square-primes but not square-$Y$-rough.
--
--   It bounds the intervals rejected for the second reason of Step 5, which are negligible in the count of Proposition 10.9.
--
--   **Formalization Note** One constant before $N$ and $Y$.
--
--   Differences from the source:
--   - encoding: O(N^{1/2}Y^{1/2}) → one constant K before N, Y; reason: this is what the O / o(1) notation means for one algorithm (§1.1, p.1); the constants are chosen before every input
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Lemma 9.11, p.92

import Mathlib
import Definitions.Def_FasterPrimeEnum_IsSquarePrime
import Definitions.Def_FasterPrimeEnum_IsRough

set_option autoImplicit false

namespace FasterPrimeEnum

open Classical in
/-- **Lemma 9.11** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version, sha256 7fc13f17…), p.92.

"Let N and Y ⩽ N be positive integers. Then there are at most O(N^{1/2}Y^{1/2}) positive
integers n < N that are square-prime but not square-Y-rough."

**Formalization Note.** One constant before `N` and `Y`. `Y = 1` is allowed; every positive integer
is square-`1`-rough, so the count is `0` there. -/
theorem lemma_9_11 :
    ∃ K : ℝ, 0 < K ∧ ∀ N Y : ℕ, 0 < Y → Y ≤ N →
      ((((Finset.range N).filter fun n =>
          0 < n ∧ IsSquarePrime n ∧ ¬ IsSquareRough (Y : ℝ) n).card : ℕ) : ℝ) ≤
        K * Real.sqrt N * Real.sqrt Y := by sorry

end FasterPrimeEnum
