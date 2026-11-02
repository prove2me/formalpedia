-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_optimal_policy_is_fi_policy
-- name    : AllocationIndices.Precedence.optimal_policy_is_fi_policy
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T14:51:30.197127+00:00
-- url     : https://prove2.me/theorems/7d34490f-62d4-42b1-b294-e8ca296af532
-- title:
--   Theorem 4.9 (one inclusion) — every optimal policy is a forwards induction policy
-- statement:
--   Let $\mathscr F$ be a family of $n$ ordinary jobs on a single machine with precedence constraints (no circuits), no arrivals and no preemption: job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$ ($V_i>0$, $\gamma>0$), the service times $\sigma_i>0$ are independent, and a policy chooses, each time the machine becomes free, an available job as a measurable function of the jobs completed so far and their observed service times. Let $A$ be the initial set of completed jobs, and let $\nu(\cdot)$ be the index (4.15) of the family that remains, $\nu = \sup_{g,\tau} R_{g\tau}/W_{g\tau}$.
--
--   **Claim.** If $\pi$ is an optimal policy from $A$ (feasible, and its payoff $R_\pi(\mathscr F)=E\sum_{i\notin A}V_ie^{-\gamma C_i}$ is at least that of every feasible policy), then $\pi$ is a **forwards induction (FI) policy**: with probability one, at every decision time the job $\pi$ starts is the first job of some stage $(g,\tau)$ attaining the supremum $\nu(\mathscr G)$ in (4.15) for the family $\mathscr G$ that remains at that time.
--
--   This is the inclusion "optimal $\subseteq$ FI" of Theorem 4.9, which asserts that index, forwards induction and optimal policies form the same class. The printed proof (pp. 97–99) only establishes that FI\* policies are optimal (see the mission discussion), so this inclusion is the part of Theorem 4.9 not argued on the page. "With probability one" is necessary: changing an optimal policy on a null set of service-time realizations keeps it optimal.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.6 pp. 97-99, Theorem 4.9 (inclusion of the optimal policies in the forwards induction policies)

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem optimal_policy_is_fi_policy {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) (hπ : IsOptimalPolicy F A π) : IsFIPolicy F A π := by sorry

end AllocationIndices.Precedence
