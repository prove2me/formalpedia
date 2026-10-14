-- Prove2me | Theorems.Thm_BudgetClock_PostedLB_case_3
-- name    : BudgetClock.PostedLB.case_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:19.018104+00:00
-- url     : https://prove2.me/theorems/b3712cf3-a4c0-41ba-af45-56df6d288bb0
-- title:
--   Theorem 13 proof, Case 3, p. 25 — price 0 before b_h, then p_h < B to b_h: v(M) ≤ 1 < √n
-- statement:
--   Let $B>0$ and let $M$ be a deterministic posted-price mechanism that is budget feasible for additive valuations. Run $M$ with the valuation $v_0$ of the hard family on the profile where every seller has cost $B$, and suppose that every offer made before $b_h$ is approached is at most $0$ and that $b_h$ is offered a price $p_h<B$. Write $c^B$ for this all-$B$ profile. Then on $c^B$ the mechanism obtains value at most $1$, the set $\{b_h\}$ fits the budget, and
--   $$\frac{\sqrt n}{2}\,v_0(M(c^B))\;<\;\sqrt n=v_0(\{b_h\}).$$
--
--   This is the third case of the proof of Theorem 13: a mechanism that underbids the high-value bidder loses it, and with every cost equal to $B$ it can afford at most one small bidder.
--
--   **Formalization Note** "Price $0$" is rendered as "price at most $0$", as in Cases 1 and 2. The run of the hypothesis and of the conclusion is the same run, on the all-$B$ profile.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, proof of Theorem 13, Case 3

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_HardInstance

namespace BudgetClock.PostedLB

theorem case_3 (n : ℕ) (B : ℝ) (hB : 0 < B)
    (M : (Finset (Fin n) → ℝ) → PostedPrice n) (hM : BudgetFeasible B M)
    (pre post : List (Offer n)) (b : Fin n) (ph : ℝ) (a : Bool)
    (hrun : run (M (hardVal n)) (allCostB n B) = pre ++ (b, ph, a) :: post)
    (hb : b.val = 0) (hph : ph < B)
    (hpre : ∀ e ∈ pre, e.2.1 ≤ 0) :
    hardVal n (accepted (run (M (hardVal n)) (allCostB n B))) ≤ 1 ∧
      ∑ j ∈ highSet n, allCostB n B j ≤ B ∧
      Real.sqrt (n : ℝ) / 2 * hardVal n (accepted (run (M (hardVal n)) (allCostB n B))) <
        hardVal n (highSet n) := by sorry

end BudgetClock.PostedLB
