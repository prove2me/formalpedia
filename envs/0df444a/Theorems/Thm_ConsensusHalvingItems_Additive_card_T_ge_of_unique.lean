-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_card_T_ge_of_unique
-- name    : ConsensusHalvingItems.Additive.card_T_ge_of_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:40.629418+00:00
-- url     : https://prove2.me/theorems/f025e5a8-af0d-43ea-b5ad-40591b3a42c6
-- title:
--   Proof of Theorem 2.2: at termination $|T| \ge m - n$
-- statement:
--   Let $u$ be the additive utilities of $n$ agents over $m$ items, $T$ a set of items, and $x$ a solution of the system $S$. If $x$ is the unique solution of $S \cup T$, then
--
--   $$
--   |T| \ge m - n .
--   $$
--
--   Together with the invariant that every item of $T$ is uncut, this bounds the number of cut items in the output by $n$.
--
--   **Formalization Note** The inequality is written $m \le n + |T|$, which avoids truncated subtraction of natural numbers.
--
--   Differences from the source:
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - generalization: the end of the algorithm, under the assumption n ≤ m → every n, every T and every x solving S that is the unique solution of S ∪ T; reason: the final state satisfies these hypotheses; for n ≤ m the statement is the paper's
--   - encoding: |T| ≥ m − n → m ≤ n + T.card; reason: avoids truncated natural-number subtraction; equivalent
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶5, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesST

namespace ConsensusHalvingItems.Additive

/-- **At termination |T| ≥ m − n.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶5, p. 5: "When the while loop in Step 3
terminates, (x1, . . . , xm) must be the unique solution to S ∪ T. Recall that a system of linear
equations with m variables can only have a unique solution when the number of constraints is at
least m. This means that |S ∪ T| ≥ m at the end of the algorithm. Since |S| = n, we must have
|T| ≥ m − n, as desired."

If `x` solves S and is the only solution of S ∪ T, then `m ≤ n + |T|`.

**Formalization Note.** `|T| ≥ m − n` is written `m ≤ n + T.card`, which avoids truncated
subtraction on ℕ; it holds for every `n` (no assumption `n ≤ m`). -/
theorem card_T_ge_of_unique {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by sorry

end ConsensusHalvingItems.Additive
