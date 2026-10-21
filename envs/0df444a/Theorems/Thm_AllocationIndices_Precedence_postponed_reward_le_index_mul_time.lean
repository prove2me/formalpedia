-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_postponed_reward_le_index_mul_time
-- name    : AllocationIndices.Precedence.postponed_reward_le_index_mul_time
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:18.798389+00:00
-- url     : https://prove2.me/theorems/d8f76d9a-3bcd-4916-8f6d-0e0f8f5f3a2b
-- title:
--   Eq. (4.16) — postponing the first-stage rewards does not raise their rate: $R_{g\pi\sigma}(\mathscr F) \le W_{g\pi\sigma}(\mathscr F)\,\nu(\mathscr F)$
-- statement:
--   Let $\mathscr F$ be a family of $n$ ordinary jobs on a single machine with precedence constraints (no circuits), no arrivals and no preemption: job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$, $V_i > 0$, $\gamma > 0$, and the service times $\sigma_i > 0$ are independent. Let $B$ be the set of jobs already completed and $\nu(\mathscr F)$ the index (4.15) of the family. Let $(\pi, \sigma)$ be the first stage of a modified forwards induction policy, i.e. a stage attaining the supremum in (4.15), which serves a fixed subset of jobs in a fixed order (respecting the precedence constraints) until all of them are complete. Then for every feasible non-preemptive policy $g$,
--   $$R_{g\pi\sigma}(\mathscr F) \le W_{g\pi\sigma}(\mathscr F)\,\nu(\mathscr F),$$
--   where $R_{g\pi\sigma}(\mathscr F)$ and $W_{g\pi\sigma}(\mathscr F)$ are the expected discounted rewards and the expected discounted time accruing under $g$ to the jobs of the first stage of $(\pi, \sigma)$: each such job $i$ contributes $V_i e^{-\gamma C_i}$ and $\int_{S_i}^{C_i} e^{-\gamma t}\,dt$, with $S_i, C_i$ its start and completion times under $g$.
--
--   This is inequality (4.16) in the special case of Theorem 4.9, where the book's proof establishes it: a policy other than $\pi$ only postpones the accrual of the rewards that the first stage of an FI\* policy would have collected, and doing so cannot raise their equivalent reward rate above the index of the family.
--
--   **Formalization Note** The first stage is required to be static (`Stage.IsStatic`: its choices and its stopping decisions depend only on how many jobs it has completed), which is the form the book's proof of Theorem 4.9 gives it ("a modified forwards induction policy is a policy which chooses a subset of jobs and (respecting the precedence constraints) processes them in some order until all are complete"); the general first stage of (4.15) may be adaptive (finding F2). Units are the book's continuous-time units: $W = \gamma^{-1}E(1 - e^{-\gamma T})$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.6 p. 97, Eq. (4.16) (established for this model in the proof of Theorem 4.9, pp. 98–99)

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem postponed_reward_le_index_mul_time {n : ℕ} (F : JobFamily n) (B : Finset (Fin n))
    (p : Stage n) (hp : IsFIStarStage F B p) (hstatic : p.IsStatic)
    (g : Policy n) (hg : g.Feasible F B) :
    postponedReward F B p g ≤ postponedTime F B p g * familyIndex F B := by sorry

end AllocationIndices.Precedence
