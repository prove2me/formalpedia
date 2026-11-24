-- Prove2me | Theorems.Thm_EWILI2018_scheduler_call_conditions
-- name    : EWILI2018.scheduler_call_conditions
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T07:59:12.891833+00:00
-- url     : https://prove2.me/theorems/9c7beef1-68a4-432c-a30c-ac0d54632fea
-- title:
--   Necessary and sufficient conditions to call the scheduler from `running`
-- statement:
--   Formalizes the Section 5 analysis of Figure 4 (`schedulerSpec`) starting from the $\mathsf{running}$ state:
--
--   1. In state $\mathsf{running}$, `scheduleEntry` has no defined transition, and the only defined outgoing events are `schedSetStateSleepable` and `schedNeedResched`.
--   2. Every finite sequence $u$ leading from $\mathsf{running}$ to a state $q$ where `scheduleEntry` is defined must be non-empty and begin with either `schedSetStateSleepable` or `schedNeedResched`.
--   3. Taking `schedSetStateSleepable` reaches $\mathsf{sleepable}$ where `scheduleEntry` is enabled, yet `[schedSetStateRunnable]` returns directly to $\mathsf{running}$ without invoking `scheduleEntry`.
--   4. Taking `schedNeedResched` reaches $\mathsf{preemptionRunnable}$ where `scheduleEntry` is enabled, and every finite sequence $u$ returning from $\mathsf{preemptionRunnable}$ to $\mathsf{running}$ satisfies
--
--   $$\hat{\delta}_{\mathrm{spec}}(\mathsf{preemptionRunnable}, u) = \mathsf{running} \implies \mathsf{schedSwitchPreempt} \in u.$$
--
--   This captures the asymmetry between voluntary sleep preparation (reversible without a context switch) and `need_resched` preemption.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §5, Fig. 4, pp. 4–5. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=5

import Definitions.Def_EWILI2018_SchedulerSpec
open RamadgeWonham.Shared

namespace EWILI2018
theorem scheduler_call_conditions :
    schedulerSpec.δ .scheduleEntry .running = none ∧
    (∀ e : SchedulerSpecEvent,
      (schedulerSpec.δ e .running).isSome = true ↔
        e = .schedSetStateSleepable ∨ e = .schedNeedResched) ∧
    (∀ u : List SchedulerSpecEvent, ∀ q : SchedulerSpecState,
      schedulerSpec.runFrom .running u = some q →
      (schedulerSpec.δ .scheduleEntry q).isSome = true →
      ∃ e rest, u = e :: rest ∧ (e = .schedSetStateSleepable ∨ e = .schedNeedResched)) ∧
    (schedulerSpec.δ .schedSetStateSleepable .running = some .sleepable ∧
      (schedulerSpec.δ .scheduleEntry .sleepable).isSome = true ∧
      schedulerSpec.runFrom .sleepable [.schedSetStateRunnable] = some .running ∧
      SchedulerSpecEvent.scheduleEntry ∉ ([.schedSetStateRunnable] : List SchedulerSpecEvent)) ∧
    (schedulerSpec.δ .schedNeedResched .running = some .preemptionRunnable ∧
      (schedulerSpec.δ .scheduleEntry .preemptionRunnable).isSome = true ∧
      ∀ u : List SchedulerSpecEvent,
        schedulerSpec.runFrom .preemptionRunnable u = some .running →
        .schedSwitchPreempt ∈ u) := by sorry
end EWILI2018
