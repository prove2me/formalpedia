-- Prove2me | Theorems.Thm_FixedMachinePrec_theorem_5_12
-- name    : FixedMachinePrec.theorem_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:01.534994+00:00
-- url     : https://prove2.me/theorems/a6daf6fd-b277-4e33-939c-f6126990fb90
-- title:
--   Theorem 5.12 — Algorithms 6 and 7 are correct
-- statement:
--   Let $m\ge3$ and let $G$ be an acyclic instance.
--
--   1. For every deadline $T$, Algorithm 6 answers NO if and only if no feasible schedule has makespan at most $T$; every schedule it returns is feasible with makespan at most $T$.
--   2. Algorithm 7 returns $(u,\sigma)$ where $\sigma$ is an optimum schedule — its makespan is at most that of every feasible schedule with real start times — and $u=C_{\max}(\sigma)$.
--
--   **Formalization Note** Returned schedules are integral and read in real time with start $=$ slot $-1$.
--
--   Differences from the source:
--   - encoding: a returned slot schedule → an integral schedule realizing a real-time schedule (start = slot − 1, same machines); reason: the paper's slot t means execution during [t − 1, t)
--   - encoding: “return an optimum schedule” with value u → σ optimum among real-time schedules and u = Cmax(σ); reason: the proof states that u is the smallest feasible deadline and equals the continuous-time optimum
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 5.12, p.20

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline

namespace FixedMachinePrec

/-- **Theorem 5.12 (Correctness of the deadline and optimization algorithms).** Jansen, *Precedence
Constraint Scheduling on a Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Theorem 5.12,
p.20: "For m ≥ 3, Algorithms 6 and 7 decide deadline feasibility exactly and return an optimum
schedule, respectively."

For `m ≥ 3` and every acyclic instance:
1. for every deadline `T`, Algorithm 6 answers NO exactly when no feasible schedule has makespan at
   most `T`, and every schedule it returns is feasible with makespan at most `T`;
2. Algorithm 7 returns `(u, σ)` with `σ` an optimum schedule (against all feasible schedules with
   real start times) and `u` its makespan.

**Formalization Note** Returned schedules are integral; they are read in real time through
`Realizes` (`start = slot − 1`). The proof's last sentence ("this integer optimum also equals the
continuous-time optimum") is part of the claim. -/
theorem theorem_5_12 (m : ℕ) (hm : 3 ≤ m) (G : Instance) (hG : G.Acyclic) :
    (∀ T : ℕ, (deadline G m T = none ↔ ¬ DeadlineFeasible G m T) ∧
      ∀ σ, deadline G m T = some σ → σ.MeetsDeadline m T) ∧
    (∃ ρ : Schedule G m, (optimum G m).2.Realizes ρ ∧ IsOptimum ρ ∧
      ρ.cmax = ((optimum G m).1 : ℝ)) := by sorry

end FixedMachinePrec
