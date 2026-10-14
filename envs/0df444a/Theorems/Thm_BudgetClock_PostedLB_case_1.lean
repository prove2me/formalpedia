-- Prove2me | Theorems.Thm_BudgetClock_PostedLB_case_1
-- name    : BudgetClock.PostedLB.case_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:22.567602+00:00
-- url     : https://prove2.me/theorems/6267e8b1-dbe6-4e5f-ae38-9bb9f72ec5ff
-- title:
--   Theorem 13 proof, Case 1, p. 25 — first positive offer goes to a small bidder before b_h: v(M) ≤ 1 < √n
-- statement:
--   Let $B>0$ and let $M$ be a deterministic posted-price mechanism that is budget feasible for additive valuations. Run $M$ with the valuation $v_0$ of the hard family (bidder $b_h$ of value $\sqrt n$, the others of value $1$) on the profile where every seller has cost $B$, and suppose that, in this run, some small bidder $i$ receives an offer $p_i>0$ while every earlier offer went to a small bidder and was at most $0$; in particular $b_h$ has not been approached yet. Let $c$ be the cost profile with $c_i=p_i$ and $c_j=B$ for every $j\neq i$. Then on $c$ the mechanism obtains value at most $1$, the set $\{b_h\}$ fits the budget, and
--   $$\frac{\sqrt n}{2}\,v_0(M(c))\;<\;\sqrt n=v_0(\{b_h\}).$$
--
--   This is the first of the three cases into which the proof of Theorem 13 splits every mechanism. When the first positive offer goes to a small bidder, making that bidder accept exhausts the mechanism's room to buy anything else.
--
--   **Formalization Note** "Before $b_h$" and "the first small value bidder the mechanism makes a positive offer to" are read off the run on the all-$B$ profile: its history is `pre ++ (i, p_i, a) :: post` with every entry of `pre` a small bidder offered a non-positive price. Until $i$ is approached the run on $c$ makes the same offers (every seller rejects a non-positive price, and $b_h$ is not involved), so this is the paper's "first positive offer" for the Case 1 instance. The paper says "price $0$"; a non-positive price is the exact complement of "positive", since the model allows any real price.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 25, proof of Theorem 13, Case 1

import Mathlib
import Definitions.Def_BudgetClock_PostedLB_HardInstance

namespace BudgetClock.PostedLB

theorem case_1 (n : ℕ) (B : ℝ) (hB : 0 < B)
    (M : (Finset (Fin n) → ℝ) → PostedPrice n) (hM : BudgetFeasible B M)
    (pre post : List (Offer n)) (i : Fin n) (p : ℝ) (a : Bool)
    (hrun : run (M (hardVal n)) (allCostB n B) = pre ++ (i, p, a) :: post)
    (hi : i.val ≠ 0) (hp : 0 < p)
    (hpre : ∀ e ∈ pre, e.1.val ≠ 0 ∧ e.2.1 ≤ 0) :
    hardVal n (accepted (run (M (hardVal n)) (case1Cost n B i p))) ≤ 1 ∧
      ∑ j ∈ highSet n, case1Cost n B i p j ≤ B ∧
      Real.sqrt (n : ℝ) / 2 * hardVal n (accepted (run (M (hardVal n)) (case1Cost n B i p))) <
        hardVal n (highSet n) := by sorry

end BudgetClock.PostedLB
