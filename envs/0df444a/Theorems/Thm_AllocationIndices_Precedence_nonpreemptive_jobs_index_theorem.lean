-- Prove2me | Theorems.Thm_AllocationIndices_Precedence_nonpreemptive_jobs_index_theorem
-- name    : AllocationIndices.Precedence.nonpreemptive_jobs_index_theorem
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:18.268407+00:00
-- url     : https://prove2.me/theorems/a8ec8da3-e4c5-4049-8885-9f134fc6e46f
-- title:
--   Theorem 4.9 — the index theorem for non-preemptive scheduling of ordinary jobs with precedence constraints
-- statement:
--   Let $\mathscr F$ be a family of alternative bandit processes all of which are jobs with a single reward upon completion, with arbitrary precedence constraints, no arrivals, and no preemption. Concretely, there are $n$ jobs on a single machine; job $i$ yields the reward $V_i e^{-\gamma C_i}$ at its completion time $C_i$, where $V_i > 0$ and $\gamma > 0$, and no other reward; the service times $\sigma_1, \dots, \sigma_n$ are independent, each positive with probability one; a relation $i \prec j$ without circuits says that job $i$ must be completed before job $j$ may be started; once started, a job is served until it is completed. A policy chooses, each time the machine becomes free, an available job as a function of the jobs completed so far and their observed service times, and its payoff is $R_g(\mathscr F) = E\sum_i V_i e^{-\gamma C_i}$.
--
--   Let $\nu(\mathscr F) = \sup_{g,\tau} R_{g\tau}(\mathscr F)/W_{g\tau}(\mathscr F)$ be the index (4.15) of the family, the supremum over policies $g$ and positive stopping times $\tau$ of the expected discounted reward up to $\tau$ divided by the expected discounted time $W_{g\tau}(\mathscr F) = \gamma^{-1}E(1 - e^{-\gamma T})$, $T$ the time at which $\tau$ ends the stage. A **modified forwards induction (FI\*) policy** repeatedly begins a stage $(\pi,\sigma)$ attaining this supremum for the family that remains and follows it to its end; a **forwards induction (FI) policy** starts, at every decision time, a job with which such a stage begins.
--
--   **Theorem 4.9.** From every initial set $A$ of completed jobs, the following three classes of policies are identical:
--   1. the index policies, i.e. the modified forwards induction policies built from the index (4.15);
--   2. the forwards induction policies;
--   3. the optimal policies, those maximizing $R_g(\mathscr F)$ over all feasible non-preemptive policies.
--
--   Partial results in this direction were obtained by Sidney (1975), Kadane and Simon (1977) and Glazebrook and Gittins (1981). The theorem says that the optimal non-preemptive schedule of a stochastic precedence-constrained job family is built greedily from initial portions of maximal equivalent reward rate, and that, conversely, only such schedules are optimal.
--
--   **Formalization Note** The book does not define index policies for a family that is not simple; class 1 is read as the class of modified forwards induction (FI\*) policies, which the book identifies with modified index policies (p. 33). The three classes are compared up to service-time realizations of probability zero: a policy is FI or FI\* if it behaves as such with probability one, which is the only sense in which "identical" can hold, since changing an optimal policy on a null set of realizations leaves it optimal. Policies are deterministic functions of the observed history and never idle; the payoff and the index are in the book's continuous-time units. The printed proof establishes only that FI\* policies are optimal (finding F1).
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.6 p. 98, Theorem 4.9

import Definitions.Def_AllocationIndices_Precedence_Model

open MeasureTheory

namespace AllocationIndices.Precedence

theorem nonpreemptive_jobs_index_theorem {n : ℕ} (F : JobFamily n) (A : Finset (Fin n))
    (π : Policy n) :
    (IsFIStarPolicy F A π ↔ IsFIPolicy F A π) ∧
      (IsFIPolicy F A π ↔ IsOptimalPolicy F A π) := by sorry

end AllocationIndices.Precedence
