-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_items_bound
-- name    : ComplementFreeCA.CFRounding.items_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:17:47.506678+00:00
-- url     : https://prove2.me/theorems/5ecb2315-4732-4315-a49c-2e8a14c5e227
-- title:
--   §3.1.1 — with probability ≥ 1 − 1/m no item appears more than 3 log m / log log m times
-- statement:
--   There is $m_0$ such that for every $m\ge m_0$, every number $n$ of bidders and every LP-feasible $x$, the randomized-rounding preallocation $\sigma=(S_1,\dots,S_n)$ satisfies:
--
--   1. for each item $j$,
--   $$\Pr\Big[j \text{ appears in more than } \tfrac{3\log m}{\log\log m} \text{ of the bundles } S_1,\dots,S_n\Big]\le\frac1{m^2};$$
--   2. by the union bound over the $m$ items,
--   $$\Pr\Big[\text{some item appears in more than } \tfrac{3\log m}{\log\log m} \text{ bundles}\Big]\le\frac1{m}.$$
--
--   This is the first half of the analysis of step (i) of the algorithm in §3.1.1: with high probability the preallocation violates each item constraint by at most a factor $k$.
--
--   **Formalization Note** The paper's display after Lemma 3.1 prints the threshold as $\log m/(3\log\log m)$, a slip for the lemma's $3\log m/\log\log m$ (with the smaller threshold the $1/m^2$ bound fails); the statement uses $3\log m/\log\log m$. The probability is the finite-sum rounding probability of the LP definition file; $\log$ is the natural logarithm; $m_0$ is existential because Lemma 3.1 holds for sufficiently large $m$.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1.1, display after Lemma 3.1 and the union-bound sentence that follows

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm

namespace ComplementFreeCA.CFRounding

theorem items_bound :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (n : ℕ) (x : Fin n → Finset (Fin m) → ℝ), IsLPFeasible x →
      (∀ j : Fin m, roundProb x
          (fun σ => 3 * Real.log m / Real.log (Real.log m) < (count σ j : ℝ)) ≤ 1 / (m : ℝ) ^ 2) ∧
      roundProb x
          (fun σ => ∃ j : Fin m, 3 * Real.log m / Real.log (Real.log m) < (count σ j : ℝ))
        ≤ 1 / (m : ℝ) := by sorry

end ComplementFreeCA.CFRounding
