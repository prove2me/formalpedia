-- Prove2me | Theorems.Thm_EvasivePatterns_hhs_upper_bound
-- name    : EvasivePatterns.hhs_upper_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:06.724956+00:00
-- url     : https://prove2.me/theorems/25ac046c-c3ca-46b7-b1bc-9c031d46e00f
-- title:
--   [HHS18, Lemma 8] — universal upper bound $D_P(n)\le n-(n\bmod c)$
-- statement:
--   For every binary pattern $P$ with $c = \gcd \mathrm{Per}(P)$ and every text length $n$,
--   $$
--   D_P(n) \le n - (n \bmod c) .
--   $$
--   This upper bound of He, Huang and Sun (*Almost Tight Bounds on the Query Complexity of String Matching*, ESA 2018, Lemma 8) is cited by the paper in the proof of Theorem 1.1, where it supplies the matching upper bound.
--
--   Differences from the source:
--   - generalization: binary pattern P (the paper's patterns have a smallest period, hence are nonempty) → any P : List Bool, the empty word included; reason: the statement also holds for the empty word, so it specializes to the source's claim for every nonempty P
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), proof of Theorem 1.1, §6, p.9 (PDF p.10), lines 300–301 (citing [HHS18, Lemma 8])

import Mathlib
import Definitions.Def_EvasivePatterns_periods
import Definitions.Def_EvasivePatterns_queryComplexity

namespace EvasivePatterns

/-- **The universal upper bound of He, Huang and Sun [HHS18, Lemma 8], as used in the paper.**
`D_P(n) ≤ n − (n mod c)`, where `c = gcd Per(P)`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), proof of Theorem 1.1, §6, printed p. 9 (PDF p. 10), lines 300–301: "The universal
upper bound of He, Huang and Sun [HHS18, Lemma 8] is D_P(n) ≤ n − (n mod c)", citing K. He, Q. Huang,
X. Sun, *Almost Tight Bounds on the Query Complexity of String Matching* (ESA 2018), Lemma 8. Cited
(not proved) by the paper.

**Formalization Note** `P` is a binary word (`List Bool`), `c = gcdPeriods P` (`≥ 1` for a nonempty
word); the empty word (`c = 0`, `n % 0 = n`, `D_P ≡ 0`) is not excluded. The bound holds for every `n` (no hypothesis `c < p`: "universal"). `n − (n mod c)` is exact in `ℕ`. -/
theorem hhs_upper_bound (P : List Bool) (n : ℕ) :
    queryComplexity P n ≤ n - n % gcdPeriods P := by sorry

end EvasivePatterns
