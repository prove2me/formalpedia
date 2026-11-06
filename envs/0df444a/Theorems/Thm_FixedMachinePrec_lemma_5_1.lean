-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_5_1
-- name    : FixedMachinePrec.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:12.721129+00:00
-- url     : https://prove2.me/theorems/c4a11031-a397-4dbe-9115-5295c6c78b9a
-- title:
--   Lemma 5.1 — integral slots suffice
-- statement:
--   Let $m\ge1$, let $G$ be an acyclic instance, and let $\sigma$ be a feasible nonpreemptive schedule of its unit jobs on $m$ machines with nonnegative real start times. Then there are a deadline $T$ and a slot schedule $\tau$ of deadline $T$ — every job gets a slot $\tau(x)\in\{1,\dots,T\}$, every slot holds at most $m$ jobs, and $\tau(x)<\tau(y)$ whenever $x\prec y$ — with
--   $$T\le C_{\max}(\sigma).$$
--
--   Integral slots therefore lose no optimality: the optimum over real-time schedules is attained by a slot schedule.
--
--   **Formalization Note** "No larger makespan" is stated as $T\le C_{\max}(\sigma)$, which bounds the last used slot.
--
--   Differences from the source:
--   - generalization: the scope m ≥ 3 of the explicit procedures (p.1) → every m ≥ 1; reason: the lemma and its proof place no restriction on m; m ≥ 3 is a case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
--   - encoding: a slot schedule of no larger makespan → a slot schedule of some deadline T with T ≤ Cmax(σ); reason: the makespan of a slot schedule of deadline T is at most T; same content
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 5.1, p.12

import Mathlib
import Definitions.Def_FixedMachinePrec_Instance

namespace FixedMachinePrec

/-- **Lemma 5.1 (Why integral slots suffice).** Jansen, *Precedence Constraint Scheduling on a
Fixed Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 5.1, p.12: "Every feasible
nonpreemptive unit-job schedule with nonnegative real start times can be replaced by a slot
schedule of no larger makespan."

For every feasible schedule `σ` with real start times there are a deadline `T` and a slot
schedule `τ` of deadline `T` (slots in `{1, …, T}`, at most `m` jobs per slot, `τ(x) < τ(y)`
whenever `x ≺ y`) with `T ≤ Cmax(σ)`.

**Formalization Note** The makespan of a slot schedule of deadline `T` is at most `T`; asking for
`T ≤ Cmax(σ)` is "no larger makespan". Feasibility of `σ` already contains nonnegative start
times. -/
theorem lemma_5_1 (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) (σ : Schedule G m)
    (hσ : σ.Feasible) :
    ∃ (T : ℕ) (τ : Fin G.n → ℕ), IsSlotSchedule G m T τ ∧ (T : ℝ) ≤ σ.cmax := by sorry

end FixedMachinePrec
