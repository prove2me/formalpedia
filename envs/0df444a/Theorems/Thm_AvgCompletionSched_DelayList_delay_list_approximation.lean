-- Prove2me | Theorems.Thm_AvgCompletionSched_DelayList_delay_list_approximation
-- name    : AvgCompletionSched.DelayList.delay_list_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:07:16.243125+00:00
-- url     : https://prove2.me/theorems/2a552207-59e1-4c7b-a09d-ebc91e54aff7
-- title:
--   Theorem 4.13 — Delay List on a $\rho$-approximate one-machine schedule is a $((1+\beta)\rho + 1 + 1/\beta)$-approximation on $m$ machines
-- statement:
--   Let $I$ be an instance of scheduling with release dates $r_j\ge 0$, processing times $p_j>0$, weights $w_j>0$ and precedence constraints, to minimize the sum of weighted completion times. Let $S^1$ be a feasible one-machine schedule of $I$ that is within a factor $\rho$ of an optimal one-machine schedule: $\sum_j w_jC^1_j\le\rho\sum_j w_jC'_j$ for every feasible one-machine schedule $C'$ of $I$. Let $\beta>0$ and $m\ge 2$. Then every schedule $S^m$ produced by the continuous-time algorithm Delay List with parameter $\beta$ on $m$ machines using $S^1$ as the list satisfies, for every feasible $m$-machine schedule $N$ of $I$,
--   $$\sum_j w_jC^m_j\le\Bigl((1+\beta)\rho+1+\frac1\beta\Bigr)\sum_j w_jC^N_j .$$
--
--   This is the paper's general conversion theorem: any one-machine approximation algorithm for a scheduling problem with release dates and precedence constraints yields an $m$-machine approximation algorithm, losing at most the factor $1+\beta$ on $\rho$ and the additive $1+1/\beta$; for $\rho=1$ and $\beta=1$ it gives the factor $4$.
--
--   **Formalization Note** The optimum is not formed as an infimum: both the $\rho$-hypothesis and the conclusion are quantified over every feasible schedule of the same instance (with release dates and precedence). The bound is claimed for every run of the algorithm, whatever its tie-breaking.
-- source:
--   Chekuri, Motwani, Natarajan, Stein, Approximation Techniques for Average Completion Time Scheduling, SIAM J. Comput. 31(1), 2001, p. 161, Theorem 4.13

import Mathlib
import Definitions.Def_AvgCompletionSched_DelayList_Model
import Definitions.Def_AvgCompletionSched_DelayList_Algorithm

namespace AvgCompletionSched.DelayList

/-- Theorem 4.13 (p. 161): given an instance `I` of scheduling with release dates and precedence
constraints to minimize the sum of weighted completion times, and a feasible one-machine schedule
`S^1` of `I` within a factor `ρ` of every feasible one-machine schedule of `I`, every run of the
continuous-time algorithm Delay List (`β > 0`, `m ≥ 2` machines) using `S^1` as the list gives an
`m`-machine schedule whose sum of weighted completion times is within a factor
`(1 + β) ρ + (1 + 1/β)` of that of every feasible `m`-machine schedule of `I`. -/
theorem delay_list_approximation {n m : ℕ} (I : Instance n) (hm : 2 ≤ m) (β ρ : ℝ)
    (hβ : 0 < β) (S1 : Schedule I 1) (hρ : ∀ S1' : Schedule I 1, S1.wct ≤ ρ * S1'.wct)
    (π : Fin n ≃ Fin n) (hπ : IsCompletionOrder S1 π) (D : DelayListRun I m)
    (hD : IsDelayListSchedule I m π β D) (N : Schedule I m) :
    D.wct ≤ ((1 + β) * ρ + (1 + 1 / β)) * N.wct := by sorry

end AvgCompletionSched.DelayList
