-- Prove2me | Theorems.Thm_CycleLengthsExp_BetaGraph_arithmetic_p17
-- name    : CycleLengthsExp.BetaGraph.arithmetic_p17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:25.740477+00:00
-- url     : https://prove2.me/theorems/0cecae21-3b60-4b3f-a0b0-4dc57776407b
-- title:
--   p. 17 — for β < 1/20 and large n: 2⌈log(βn)⌉ + 1 < (1/2 − 10β)n and 2⌈log_k(βn)⌉ + 1 ≤ (25/log(1/β)) log n, k = ⌊1/(4β)⌋
-- statement:
--   Let $0<\beta<1/20$, put $k=\lfloor 1/(4\beta)\rfloor$, $b_1=25/\log(1/\beta)$, and for each $n$ let $t=\lceil\log_k(\beta n)\rceil$. Then for all sufficiently large $n$,
--   $$2\lceil\log(\beta n)\rceil+1\ <\ \Bigl(\frac12-10\beta\Bigr)n \qquad\text{and}\qquad b_1\log n\ \ge\ 2t+1 .$$
--   Logarithms without a base are to base $2$.
--
--   These two inequalities make the ranges of lengths obtained from the two families of trees overlap and reach down to $b_1\log n$, which is how the proof of Theorem 3 covers the whole interval.
--
--   **Formalization Note** The page leaves "$n$ large" implicit; the first inequality fails for small $n$, so the statement has a threshold $n_0$ depending on $\beta$. The ceilings are natural-number ceilings, which agree with the integer ceilings once $\beta n\ge1$. The page's next words, "$b_2=1-14\beta$" (meaning $b_2=14\beta$), and its conclusion are not part of this statement.
-- source:
--   Friedman and Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 17, proof of Theorem 3 ("Note that for β < 1/20 we have …"); k and t from claim (1)

import Mathlib
import Definitions.Def_CycleLengthsExp_BetaGraph_Setting

namespace CycleLengthsExp.BetaGraph

/-- The arithmetic of p. 17: for `0 < β < 1/20` and all large `n`,
`2⌈log₂(βn)⌉ + 1 < (1/2 - 10β)n` and `2t + 1 ≤ b₁ log₂ n`, where `b₁ = 25/log₂(1/β)`,
`k = ⌊1/(4β)⌋` and `t = ⌈log_k(βn)⌉`. -/
theorem arithmetic_p17 (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 20) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      2 * (⌈Real.logb 2 (β * n)⌉₊ : ℝ) + 1 < (1 / 2 - 10 * β) * n ∧
      2 * (⌈Real.logb (⌊1 / (4 * β)⌋₊ : ℝ) (β * n)⌉₊ : ℝ) + 1 ≤
        25 / Real.logb 2 (1 / β) * Real.logb 2 n := by sorry

end CycleLengthsExp.BetaGraph
