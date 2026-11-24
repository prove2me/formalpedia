-- Prove2me | Theorems.Thm_EWILI2018_figure3_generators
-- name    : EWILI2018.figure3_generators
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T07:58:51.195782+00:00
-- url     : https://prove2.me/theorems/98bacb55-3860-48ca-9257-c5a5b30a6a1c
-- title:
--   Generated and marked languages of the Figure 3 plant generators
-- statement:
--   Characterizes the generated language $L(G)$ and marked language $L_m(G)$ of all three plant generators in Figure 3 of EWILI 2018:
--
--   1. For `needReschedGen`, every finite word over $\{\mathsf{schedNeedResched}\}$ belongs to both $L$ and $L_m$: $$L(\mathcal{G}_{\mathrm{NR}}) = L_m(\mathcal{G}_{\mathrm{NR}}) = \Sigma_{\mathrm{NR}}^*.$$
--   2. For `sleepRunGen`, $L_m(\mathcal{G}_{\mathrm{SR}})$ consists of concatenations of pairs $(e_i, \mathsf{schedSetStateSleepable})$ with each $e_i \in \{\mathsf{schedWaking}, \mathsf{schedSetStateRunnable}\}$, and $L(\mathcal{G}_{\mathrm{SR}})$ consists of those words optionally followed by one trailing wakeup/set-runnable event.
--   3. For `schedContextGen`, $L_m(\mathcal{G}_{\mathrm{SC}}) = \{(\mathsf{scheduleEntry}, \mathsf{scheduleExit})^n \mid n \in \mathbb{N}\}$ and $L(\mathcal{G}_{\mathrm{SC}})$ adds odd-length prefixes ending in $\mathsf{scheduleEntry}$.
--
--   These closed-form component languages describe the local plant invariants enforced when projections of a global kernel trace are checked.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §4.2, Fig. 3, p. 4. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=4

import Definitions.Def_EWILI2018_Generators
open RamadgeWonham.Shared

namespace EWILI2018
theorem figure3_generators :
    (needReschedGen.L = Set.univ ∧ needReschedGen.Lm = Set.univ) ∧
    (∀ w : List SleepRunEvent,
      (w ∈ sleepRunGen.Lm ↔
        ∃ triggers : List SleepRunEvent,
          (∀ e ∈ triggers, e = .schedWaking ∨ e = .schedSetStateRunnable) ∧
          w = triggers.flatMap (fun e ↦ [e, .schedSetStateSleepable])) ∧
      (w ∈ sleepRunGen.L ↔
        ∃ triggers : List SleepRunEvent,
          (∀ e ∈ triggers, e = .schedWaking ∨ e = .schedSetStateRunnable) ∧
          (w = triggers.flatMap (fun e ↦ [e, .schedSetStateSleepable]) ∨
            ∃ last, (last = .schedWaking ∨ last = .schedSetStateRunnable) ∧
              w = triggers.flatMap (fun e ↦ [e, .schedSetStateSleepable]) ++ [last]))) ∧
    (∀ w : List SchedContextEvent,
      (w ∈ schedContextGen.Lm ↔
        ∃ n : Nat, w = (List.replicate n [.scheduleEntry, .scheduleExit]).flatten) ∧
      (w ∈ schedContextGen.L ↔
        ∃ n : Nat,
          w = (List.replicate n [.scheduleEntry, .scheduleExit]).flatten ∨
          w = (List.replicate n [.scheduleEntry, .scheduleExit]).flatten ++ [.scheduleEntry])) := by sorry
end EWILI2018
