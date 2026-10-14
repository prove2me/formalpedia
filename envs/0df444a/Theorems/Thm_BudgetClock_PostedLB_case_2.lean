-- Prove2me | Theorems.Thm_BudgetClock_PostedLB_case_2
-- name    : BudgetClock.PostedLB.case_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:26.683527+00:00
-- url     : https://prove2.me/theorems/61cfeaac-c403-4a8d-b55d-b671dda02fb8
-- title:
--   Theorem 13 proof, Case 2, p. 25 — price 0 before b_h, then B to b_h: v(M) = √n and (√n/2)·v(M) < n − 1
-- statement:
--   Let $n\ge 3$, $B>0$, and let $M$ be a deterministic posted-price mechanism that is budget feasible for additive valuations. Run $M$ with the valuation $v_0$ of the hard family on the profile where every seller has cost $B$, and suppose that every offer made before $b_h$ is approached is at most $0$, and that $b_h$ is offered the entire budget $B$. Let $c$ be the profile with $c_{b_h}=B$ and $c_i=B/(n-1)$ for every small bidder $i$. Then
--
--   1. the $n-1$ small bidders together fit the budget: $\sum_{i\neq b_h}c_i\le B$;
--   2. their value is $v_0(N\setminus\{b_h\})=n-1$;
--   3. on $c$ the mechanism obtains exactly $v_0(M(c))=\sqrt n$;
--   4. and
--   $$\frac{\sqrt n}{2}\,v_0(M(c))\;<\;n-1 .$$
--
--   This is the second case of the proof of Theorem 13: a mechanism that spends its whole budget on the high-value bidder misses the $n-1$ small bidders, who together are worth more.
--
--   **Formalization Note** The page prints the small bidders' cost as $1/(n-1)$, which makes the set of small bidders budget feasible only when $B\ge1$; the cost $B/(n-1)$ is used (it agrees with the page at $B=1$). The hypothesis $n\ge3$ is needed for the strict inequality: $(n-1)/\sqrt n>\sqrt n/2$ is equivalent to $n>2$. The case hypothesis is stated on the run on the all-$B$ profile, as in Case 1; up to $b_h$'s offer the run on $c$ makes the same offers. "Price $0$" is rendered as "price at most $0$", as in Case 1.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, proof of Theorem 13, Case 2

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_HardInstance

namespace BudgetClock.PostedLB

theorem case_2 (n : ℕ) (hn : 3 ≤ n) (B : ℝ) (hB : 0 < B)
    (M : (Finset (Fin n) → ℝ) → PostedPrice n) (hM : BudgetFeasible B M)
    (pre post : List (Offer n)) (b : Fin n) (a : Bool)
    (hrun : run (M (hardVal n)) (allCostB n B) = pre ++ (b, B, a) :: post)
    (hb : b.val = 0)
    (hpre : ∀ e ∈ pre, e.2.1 ≤ 0) :
    ∑ j ∈ smallSet n, case2Cost n B j ≤ B ∧
      hardVal n (smallSet n) = (n : ℝ) - 1 ∧
      hardVal n (accepted (run (M (hardVal n)) (case2Cost n B))) = Real.sqrt (n : ℝ) ∧
      Real.sqrt (n : ℝ) / 2 * hardVal n (accepted (run (M (hardVal n)) (case2Cost n B))) <
        hardVal n (smallSet n) := by sorry

end BudgetClock.PostedLB
