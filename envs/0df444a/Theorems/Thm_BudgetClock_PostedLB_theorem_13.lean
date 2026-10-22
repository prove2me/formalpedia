-- Prove2me | Theorems.Thm_BudgetClock_PostedLB_theorem_13
-- name    : BudgetClock.PostedLB.theorem_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:24.415731+00:00
-- url     : https://prove2.me/theorems/0cc60f1c-cf75-4ad0-839a-8552c86fd9c4
-- title:
--   Theorem 13, p. 25 — no deterministic budget-feasible posted-price mechanism beats √n/2 for additive valuations
-- statement:
--   **Theorem 13.** No deterministic posted-price mechanism can achieve an approximation better than $\sqrt n/2$ for instances with additive valuation functions.
--
--   Precisely: let $n\ge1$ be the number of sellers and $B>0$ the budget, and let $M$ be any deterministic posted-price mechanism that is budget feasible on every instance with an additive valuation (for every additive $v$ and every cost profile $c\ge0$, the accepted prices sum to at most $B$). Then there are an additive valuation $v$, a cost profile $c\ge 0$ and a set $O$ of sellers with
--   $$\sum_{i\in O}c_i\le B,\qquad v(O)>0,\qquad \frac{\sqrt n}{2}\,v\big(M(v,c)\big)\le v(O),$$
--   where $M(v,c)$ is the set of sellers who accept in the run of $M$ on this instance. Since $O$ is budget feasible at the true costs, $\mathrm{OPT}\ge v(O)$, so the instance has $\mathrm{OPT}/v(M)\ge\sqrt n/2$ (with ratio $+\infty$ when $v(M)=0$).
--
--   The result shows that, unlike clock auctions, posted-price mechanisms cannot reach a constant approximation even for additive valuations, which is the motivation of Appendix B.
--
--   **Formalization Note** The approximation ratio is stated in multiplied form, so there is no division by a possibly zero $v(M)$; the requirement $v(O)>0$ keeps the instance from being one where every mechanism is trivially optimal. The quantifiers are "for every mechanism there is an instance". The budget $B>0$ is an addition (§2 says only "a budget $B$"); with $B=0$ there is nothing to buy. The page states no range of $n$; $n\ge1$ excludes only the empty seller set, where $v(O)>0$ is impossible. For $n\le 4$ the bound $\sqrt n/2\le1$ is the trivial one. A mechanism is `M : (Finset (Fin n) → ℝ) → PostedPrice n`, so it may depend on $v$, $n$ and $B$ but not on the costs; budget feasibility quantifies over every additive valuation and every nonnegative cost profile, as on p. 24.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, Theorem 13

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_Setting

namespace BudgetClock.PostedLB

theorem theorem_13 (n : ℕ) (hn : 1 ≤ n) (B : ℝ) (hB : 0 < B)
    (M : (Finset (Fin n) → ℝ) → PostedPrice n) (hM : BudgetFeasible B M) :
    ∃ (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ), IsAdditive v ∧ (∀ i, 0 ≤ c i) ∧
      ∃ O : Finset (Fin n), ∑ i ∈ O, c i ≤ B ∧ 0 < v O ∧
        Real.sqrt (n : ℝ) / 2 * v (accepted (run (M v) c)) ≤ v O := by sorry

end BudgetClock.PostedLB
