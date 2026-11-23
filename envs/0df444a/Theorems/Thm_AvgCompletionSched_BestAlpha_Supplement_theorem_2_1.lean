-- Prove2me | Theorems.Thm_AvgCompletionSched_BestAlpha_Supplement_theorem_2_1
-- name    : AvgCompletionSched.BestAlpha.Supplement.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:52:00.485567+00:00
-- url     : https://prove2.me/theorems/2dc698ca-9ef0-48ea-b2e6-afbbd7a72151
-- title:
--   Theorem 2.1 — full α-conversion bound and asymptotic sharpness
-- statement:
--   For any finite one-machine instance with processing times $p_j>0$ and release dates $r_j\ge0$, let $P$ be any feasible preemptive schedule. For every $a\in(0,1]$ and every nondecreasing ordering of its $a$-points, the resulting offline list schedule satisfies
--
--   $$\sum_j C^a_j\le\left(1+\frac1a\right)\sum_j C^P_j.$$
--
--   The constant is asymptotically sharp at every fixed $a$, including $a=1$: for every $\varepsilon>0$ there is a finite nonempty positive-size instance and an actual SRPT schedule $P$, optimal among all feasible preemptive schedules, with $\sum_j C^P_j>0$ and
--
--   $$\sum_j C^a_j>\left(1+\frac1a-\varepsilon\right)\sum_j C^P_j.$$
--
--   The sharpness clause uses the published canonical α-order with fixed job-label ties. This companion theorem combines the existing proved upper-bound component with the previously absent tightness clause; it is not a step in the proof of the published goal.
--
--   Differences from the source:
--   - encoding: finite one-machine release-date instances and α-schedules → the immutable positive-size base model, arbitrary feasible preemptive P, all α-orders and 0<α≤1; reason: these are the source upper-bound objects; no optimality restriction is placed on its universal clause
--   - encoding: asymptotic tightness for each fixed α, illustrated with zero-size jobs on p.151 → for every ε>0 a finite nonempty positive-size instance with actual optimal SRPT P and ratio greater than 1+1/α−ε; reason: p.151 explicitly permits removing zero sizes; positive tiny jobs and the fixed-label SRPT tie rule realize the same limit, including α=1
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, DOI 10.1137/S0097539797327180, pp. 150–151, Theorem 2.1

import Mathlib
import Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Objectives
import Definitions.Def_AvgCompletionSched_BestAlpha_Supplement_Events

set_option autoImplicit false

namespace AvgCompletionSched.BestAlpha.Supplement

/-- Theorem 2.1, pp.150–151: the universal conversion bound AND sharpness for every
fixed alpha, including alpha=1. The sharpness witnesses have strictly positive sizes,
and their preemptive schedules are actual SRPT runs and optimal among all feasible P. -/
theorem theorem_2_1 :
    (∀ (n : ℕ) (I : Instance n) (P : PreemptiveSchedule I)
      (a : ℝ), a ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ π : Fin n ≃ Fin n, IsAlphaOrder P a π →
        ∑ j, listCompletion I π j ≤ (1 + 1 / a) * preemptiveCost P) ∧
    (∀ a ∈ Set.Ioc (0 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ (n : ℕ) (_ : 0 < n) (I : Instance n) (P : PreemptiveSchedule I),
        IsSRPT P ∧ OptimalPreemptive P ∧ 0 < preemptiveCost P ∧
        (1 + 1 / a - ε) * preemptiveCost P < alphaCost P (fun _ => 1) a) := by sorry

end AvgCompletionSched.BestAlpha.Supplement
