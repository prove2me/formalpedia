-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_fi_policy_is_fi_star_policy
-- name    : AllocationIndices.Precedence.fi_policy_is_fi_star_policy
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T14:51:21.739074+00:00
-- url     : https://prove2.me/theorems/521b631d-5482-40ee-a408-6f6a02d633ad
-- title:
--   Theorem 4.9 (one inclusion) — every forwards induction policy is a modified forwards induction (FI*) policy
-- statement:
--   Let $\mathscr F$ be a family of $n$ ordinary jobs on a single machine with precedence constraints (no circuits), no arrivals and no preemption: job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$ ($V_i>0$, $\gamma>0$), the service times $\sigma_i>0$ are independent, and a policy chooses, each time the machine becomes free, an available job as a measurable function of the jobs completed so far and their observed service times. Let $A$ be the initial set of completed jobs, and let $\nu(\cdot)$ be the index (4.15) of the family that remains, $\nu = \sup_{g,\tau} R_{g\tau}/W_{g\tau}$.
--
--   **Claim.** If $\pi$ is a **forwards induction (FI) policy** from $A$ — feasible, and with probability one, at every decision time, it starts a job that is the first job of some stage attaining the index $\nu(\mathscr G)$ of the family $\mathscr G$ remaining at that time — then $\pi$ is a **modified forwards induction (FI\*) policy**: there is a rule $\rho$ assigning to every history $h$ (with some job still uncompleted) a stage $\rho(h)$ attaining the index (4.15) of the family remaining after $h$, such that, with probability one, $\pi$ serves the same jobs in the same order as the policy that runs the stages of $\rho$ one after another (a new stage $\rho(h)$ being begun whenever the current one ends, $h$ the history at that moment).
--
--   This is the inclusion "FI $\subseteq$ index (= FI\*) policies" of Theorem 4.9 (pp. 97–99). Together with Corollary 4.17 at $\varepsilon=0$ (FI\* policies are optimal) and the inclusion "optimal $\subseteq$ FI", it yields the three-way identity of Theorem 4.9.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.6 pp. 97-99, Theorem 4.9 (inclusion of the forwards induction policies in the modified forwards induction / index policies); §2.6.6 for FI and FI* policies

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem fi_policy_is_fi_star_policy {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) (hπ : IsFIPolicy F A π) : IsFIStarPolicy F A π := by sorry

end AllocationIndices.Precedence
