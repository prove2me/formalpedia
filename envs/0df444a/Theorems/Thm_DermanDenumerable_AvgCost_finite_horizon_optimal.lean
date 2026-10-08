-- Prove2me | Theorems.Thm_DermanDenumerable_AvgCost_finite_horizon_optimal
-- name    : DermanDenumerable.AvgCost.finite_horizon_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:20:13.673791+00:00
-- url     : https://prove2.me/theorems/d83358c1-d214-4726-aae8-b5f64c412623
-- title:
--   §3 — g_n(i) is the optimal expected cost over periods 0, …, n among all rules
-- statement:
--   Under conditions (A) and (B), let $g_n(i)$ be the value iteration of (5) and, for a rule $R \in C$, let $h_n(i) = \sum_{t=0}^{n} E_R W_t$ be the total expected cost incurred over the periods $0, 1, \dots, n$ under $R$ when $Y_0 = i$. Then for every $n$:
--
--   1. every rule does at least as badly: $g_n(i) \le h_n(i)$ for every rule $R \in C$ and every $i \in I$;
--   2. the bound is attained: some rule $R \in C$ has $h_n(i) = g_n(i)$ for every $i \in I$.
--
--   $$g_n(i) = \min_{R \in C} h_n(i).$$
--
--   This is the paper's statement that "$g_n(i)$ is the result of an optimal rule for those periods" (proof of Theorem 1). Part 1 is the inequality used there to conclude $\liminf_n h_n(i)/n \ge g$.
--
--   **Formalization Note.** The paper's phrase reads "over the periods $0, 1, \cdots,$ under $R$", with the final $n$ missing in print; the meaning, from the gloss of (5), is the periods $0, \dots, n$. No optimality equation is assumed. The minimum is over all history-dependent randomized rules.
-- source:
--   Derman, Denumerable State Markovian Decision Processes—Average Cost Criterion, Ann. Math. Statist. 37(6) (1966), p. 1549, §3, gloss of (5) and proof of Theorem 1

import Mathlib
import Definitions.Def_DermanDenumerable_AvgCost_Model
open scoped Topology
open Filter SennottDP.AvgFinite

namespace DermanDenumerable.AvgCost

/-- Derman (1966), §3, proof of Theorem 1, p. 1549: `g_n(i)` of (5) is the result of an optimal rule
for the periods `0, 1, ⋯, n`. For every `n`: (a) no rule `R ∈ C` has total expected cost
`h_n(i)` over the periods `0, ⋯, n` below `g_n(i)`, at any initial state `i`; and (b) some rule
`R ∈ C` attains `g_n(i)` at every initial state. -/
theorem finite_horizon_optimal {S Act : Type} [Countable S] (M : MDC S Act)
    (w : S → Act → ℝ) (hB : CostBounded M w) (n : ℕ) :
    (∀ (R : Policy M) (i : S), valueIter M w n i ≤ horizonCostR R w i n) ∧
      ∃ R : Policy M, ∀ i : S, horizonCostR R w i n = valueIter M w n i := by sorry

end DermanDenumerable.AvgCost
