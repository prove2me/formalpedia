-- Prove2me | Theorems.Thm_AllocationIndices_spt_minimizes_flow_time
-- name    : AllocationIndices.spt_minimizes_flow_time
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:39:46.965339+00:00
-- url     : https://prove2.me/theorems/2c4feb22-09b3-4593-83f5-53b6b94f0c12
-- title:
--   Theorem 3.7 (Baker): on m machines the flow time of deterministic jobs is minimized by scheduling in order of increasing service time, uniquely up to permuting same-level jobs between machines
-- statement:
--   **Theorem 3.7.** The flow time for a set of $n$ deterministic jobs on any fixed number $m$ of machines is minimized by scheduling in order of increasing service time. Such policies are the only optimal policies, except that for every positive integer $r$ the jobs in the $r$th position from the end of the schedule for each machine may be permuted arbitrarily between machines.
--
--   Formally, for $m \ge 1$ machines and positive service times $s_i$:
--   1. the SPT list schedule (jobs dealt out in increasing order of service time, cyclically over the machines) has flow time at most that of every schedule;
--   2. a schedule $\sigma$ has minimal flow time if and only if there is a ranking $e$ of the jobs from the longest ($e$ a bijection onto $\{0, \dots, n-1\}$ with $s_i > s_j \Rightarrow e(i) < e(j)$, ties in any order) such that every job $i$ sits at level $\lfloor e(i)/m \rfloor + 1$ from the end of its machine's schedule: the $m$ longest jobs are last on their machines, the next $m$ are second to last, and so on. These are exactly the SPT schedules, for some order of the equal jobs, up to permuting the jobs of one level between machines.
--
--   The flow time of a schedule is $\sum_i \ell_i s_i$ with $\ell_i$ the level, which is what both parts use. With pairwise distinct service times the ranking is forced, $e(i) = \#\{j : s_j > s_i\}$, and the level is $\lceil \mathrm{rank}(i)/m \rceil$. With equal service times, exchanging two equal jobs gives the SPT schedule for the other order of those jobs, so it is still one of "such policies"; the book's uniqueness clause holds as printed and is stated in full. (Checked by enumerating every schedule for $n \le 5$, $m \le 3$ and service times in $\{1, 2, 3\}$, ties included: 4308 level profiles.)
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §3.5.5 p. 73, Theorem 3.7 (Baker 1974)

import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem spt_minimizes_flow_time {n m : ℕ} (hm : 0 < m) (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) :
    (∀ σ : Schedule n m, flowTime (sptSchedule s hm) s ≤ flowTime σ s) ∧
    (∀ σ : Schedule n m,
      flowTime σ s = flowTime (sptSchedule s hm) s ↔
        ∃ e : Fin n ≃ Fin n, (∀ i j, s j < s i → e i < e j) ∧
          ∀ i, levelFromEnd σ i = (e i : ℕ) / m + 1) := by sorry

end AllocationIndices
