-- Prove2me | Theorems.Thm_BroughanRH_titchmarshDirichlet
-- name    : BroughanRH.titchmarshDirichlet
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:28:18.239865+00:00
-- url     : https://prove2.me/theorems/712b7e04-8193-4fe8-b108-68cf2168efaa
-- title:
--   Titchmarsh’s uniform prime-power bound in progressions
-- statement:
--   For all sufficiently large $x$, every $1\le q\le x$, and every reduced residue class $a$, the prime-power counting error is at most $C\sqrt{x}(\log x)^2$ with one absolute constant. This is the chapter’s Dirichlet GRH equivalent. [Source](https://math.mit.edu/~drew/grh/).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 12.13. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem titchmarshDirichlet :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in Filter.atTop,
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ x → ∀ a : ℤ, Int.gcd a (q : ℤ) = 1 →
        |(∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (q : ℤ)]),
          ArithmeticFunction.vonMangoldt n) - x / q.totient| ≤ C * Real.sqrt x * (Real.log x)^2 := by sorry

end BroughanRH
