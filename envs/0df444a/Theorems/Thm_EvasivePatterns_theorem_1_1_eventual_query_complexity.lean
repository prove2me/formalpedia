-- Prove2me | Theorems.Thm_EvasivePatterns_theorem_1_1_eventual_query_complexity
-- name    : EvasivePatterns.theorem_1_1_eventual_query_complexity
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:14.112586+00:00
-- url     : https://prove2.me/theorems/43e86ba3-316d-44b7-a1d8-9f1c9bed9716
-- title:
--   Theorem 1.1 — eventual query complexity $D_P(n)=n-(n\bmod c)$ when $c<p$
-- statement:
--   Let $P$ be a nonempty binary pattern, with smallest period $p = \min \mathrm{Per}(P)$ and $c = \gcd \mathrm{Per}(P)$, where $\mathrm{Per}(P)$ contains all positive periods, including the length $m$. If $c < p$, then there exists $N(P)$ such that
--   $$
--   D_P(n) = n - (n \bmod c) \qquad\text{for every } n \ge N(P),
--   $$
--   where $D_P(n)$ is the optimal worst-case number of queries of an adaptive deterministic decision tree deciding whether $P$ occurs in a text $X \in \{0,1\}^n$.
--
--   In particular, when $c = 1$ (and $p \ge 2$) the pattern is eventually evasive: every position must be read for all long texts. The threshold $N(P)$ is not made explicit.
--
--   Differences from the source: none.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Theorem 1.1, display (2), p.2 (PDF p.3), lines 37–38; display (1), p.1 (PDF p.2)

import Mathlib
import Definitions.Def_EvasivePatterns_periods
import Definitions.Def_EvasivePatterns_queryComplexity

namespace EvasivePatterns

/-- **Theorem 1.1 (Eventual query complexity).** Let `P` be a nonempty binary pattern, with `p` and
`c` defined in (1). If `c < p`, then there exists `N(P)` such that `D_P(n) = n − (n mod c)` for every
`n ≥ N(P)` (2).

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Theorem 1.1, display (2), printed p. 2 (PDF p. 3), lines 37–38; `p = min Per(P)`,
`c = gcd Per(P)`, display (1), printed p. 1 (PDF p. 2).

**Formalization Note** Binary patterns are `List Bool`. `p = minPeriod P` and `c = gcdPeriods P`
over `Per(P) ⊆ [1, m]` (all periods, `m` included). `D_P(n) = queryComplexity P n` is the optimal
worst-case number of queries of an adaptive deterministic decision tree computing whether `P` occurs
in `X ∈ {0,1}^n`. `N` depends only on `P` and is not bounded (the paper gives no bound). -/
theorem theorem_1_1_eventual_query_complexity (P : List Bool) (hP : P ≠ [])
    (hcp : gcdPeriods P < minPeriod P) :
    ∃ N : ℕ, ∀ n ≥ N, queryComplexity P n = n - n % gcdPeriods P := by sorry

end EvasivePatterns
