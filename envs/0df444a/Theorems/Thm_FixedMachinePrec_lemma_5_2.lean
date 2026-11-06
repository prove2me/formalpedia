-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_5_2
-- name    : FixedMachinePrec.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:08:48.676132+00:00
-- url     : https://prove2.me/theorems/deb08c15-9914-4ae6-98d3-dee3f5d9bf89
-- title:
--   Lemma 5.2 — padding a deadline
-- statement:
--   Let $m\ge1$ and let $G$ be an acyclic instance with $n>0$ jobs. Then:
--
--   1. no deadline $T<\lceil n/m\rceil$ is feasible;
--   2. every deadline $T\ge n$ is feasible;
--   3. for $\lceil n/m\rceil\le T<n$, add $mT-n$ isolated jobs and let $J$ be the resulting set of $N=mT$ jobs; the instance is feasible by $T$ if and only if $J$ has a full schedule with exactly $T$ slots of $m$ jobs each, and
--   $$N=mT\le mn.$$
--
--   Padding reduces every relevant deadline test to the existence of a full schedule, the object the evaluation algorithm decides.
--
--   **Formalization Note** Feasibility by $T$ is over schedules with real start times. The dummies are the labels $n,\dots,mT-1$ and are incomparable with every job.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: the lemma and its proof place no restriction on m ≥ 1; m ≥ 3 is a case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
--   - encoding: the original instance is feasible by T → DeadlineFeasible: some feasible schedule with real start times has Cmax ≤ T; reason: the original model has real start times (§1); same content
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 5.2, p.12

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline

namespace FixedMachinePrec

/-- **Lemma 5.2 (Padding a deadline).** Jansen, *Precedence Constraint Scheduling on a Fixed Number
of Machines* (manuscript, sha256 08cdf3e1…), Lemma 5.2, p.12: "For n > 0, a deadline below ⌈n/m⌉
is infeasible, and a deadline at least n is feasible. For a remaining deadline T, add mT − n
isolated jobs. If J is the resulting job set and N = |J| = mT, the original instance is feasible by
T if and only if J can be scheduled in T slots containing exactly m jobs each. Moreover, N ≤ mn."

For `n > 0`:
1. `T < ⌈n/m⌉` implies that no feasible schedule has makespan at most `T`;
2. `n ≤ T` implies that some feasible schedule has makespan at most `T`;
3. for `⌈n/m⌉ ≤ T < n`, the instance is feasible by `T` if and only if the padded job set
   `J = Fin (mT)` (the original jobs and `mT − n` isolated dummies) has a full schedule of `T`
   slots of exactly `m` jobs each; and `N = mT ≤ mn`.

**Formalization Note** "Feasible by T" is `DeadlineFeasible`, over schedules with real start
times. The dummies are the labels `n, …, mT − 1` and are incomparable with every job
(`paddedPrec`). -/
theorem lemma_5_2 (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) (hn : 0 < G.n) :
    (∀ T : ℕ, T < ceilDiv G.n m → ¬ DeadlineFeasible G m T) ∧
    (∀ T : ℕ, G.n ≤ T → DeadlineFeasible G m T) ∧
    (∀ T : ℕ, ceilDiv G.n m ≤ T → T < G.n →
      (DeadlineFeasible G m T ↔
        ∃ S : List (Finset (Fin (m * T))),
          IsFullSchedule (paddedPrec G (m * T)) m Finset.univ S ∧ S.length = T) ∧
      m * T ≤ m * G.n) := by sorry

end FixedMachinePrec
