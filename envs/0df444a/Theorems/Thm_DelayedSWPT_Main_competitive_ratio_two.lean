-- Prove2me | Theorems.Thm_DelayedSWPT_Main_competitive_ratio_two
-- name    : DelayedSWPT.Main.competitive_ratio_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:47:20.562101+00:00
-- url     : https://prove2.me/theorems/36bbe2cf-b0ee-42f5-ad6b-6aa160e82a18
-- title:
--   Theorem 8 — Delayed SWPT has a competitive ratio of 2
-- statement:
--   Consider the single-machine problem of minimizing total weighted completion time $\sum_j w_j C_j$ with release dates and no preemption, with integer release dates $r_j \ge 0$, integer processing times $p_j \ge 1$ and positive weights $w_j$. Let $\pi$ be the schedule produced by the online algorithm **Delayed SWPT**. Then $2$ is the least $\rho$ such that
--
--   $$\sum_{j} w_j C_j(\pi) \le \rho \sum_j w_j C_j(S)$$
--
--   for every instance and every feasible (offline) schedule $S$ of that instance. In words: Delayed SWPT is $2$-competitive, and no smaller constant is valid for this algorithm.
--
--   Since no online algorithm for this problem has a competitive ratio below 2 (Hoogeveen and Vestjens, 1996), Delayed SWPT is a best possible online algorithm; that general lower bound is not part of this statement.
--
--   **Formalization Note** The competitive ratio is defined (p. 686) as the least such $\rho$, so the statement is `IsLeast` of the set of valid $\rho$. Comparing with every feasible schedule is the same as comparing with the offline optimum and needs no existence of an optimum. The lower half concerns Delayed SWPT only (a one-job instance with $r = 0$, $p = 1$ suffices).
-- source:
--   Anderson and Potts, Online Scheduling of a Single Machine to Minimize Total Weighted Completion Time, Math. Oper. Res. 29(3) (2004), p. 696, Theorem 8; competitive ratio defined on p. 686

import Mathlib
import Definitions.Def_DelayedSWPT_Model_dswpt

namespace DelayedSWPT.Main

open DelayedSWPT.Model

/-- Theorem 8 of Anderson and Potts (2004), p. 696: Delayed SWPT has a competitive ratio of 2.
The competitive ratio (p. 686) is the least `ρ` such that on every instance the Delayed SWPT
schedule costs at most `ρ` times every feasible (offline) schedule. -/
theorem competitive_ratio_two :
    IsLeast {ρ : ℝ | ∀ (n : ℕ) (I : Instance n) (S : Fin n → ℕ), IsFeasible I.r I.p S →
      cost I.w I.p (dswpt I) ≤ ρ * cost I.w I.p S} 2 := by sorry

end DelayedSWPT.Main
