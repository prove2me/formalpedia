-- Prove2me | Theorems.Thm_EWILI2018_figure5_table2_replay
-- name    : EWILI2018.figure5_table2_replay
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T07:59:49.190565+00:00
-- url     : https://prove2.me/theorems/0ed8836d-4548-458d-ac93-bbb001a5af37
-- title:
--   Figure 5 trace replay against Table 2 and first rejected event
-- statement:
--   Replays the $9$-event `kworker/0:2` kernel trace excerpt of Figure 5 (`figure5KernelTrace`) against the Figure 4 specification (`schedulerSpec`) and its compiled transition-table monitor:
--
--   1. Projecting the first $8$ events of `figure5KernelTrace` through `schedulerSpecView` produces `table2Events`.
--   2. For every $k \in \{0, \dots, 6\}$ (Lines $1$–$7$ of Table 2), running `schedulerSpec` on the prefix of length $k + 1$ reaches the published state `table2States[k]`.
--   3. Executing the generated integer-table monitor `LinuxRV.monitor` on both `table2Events` and the full $9$-event projection halts at zero-based index $7$ (Line $8$):
--
--   $$\operatorname{monitor}(\mathcal{G}_{\mathrm{spec}}, \sigma_Q, \sigma_{\Sigma}, w_{\mathrm{tab}}) = \mathrm{error}\bigl(7, \sigma_Q(\mathsf{running}), \sigma_{\Sigma}(\mathsf{scheduleEntry})\bigr).$$
--
--   This formalizes the paper's empirical detection of the redundant second `__schedule()` call while already in $\mathsf{running}$.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §5, Fig. 5 and Table 2, p. 5. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=5

import Definitions.Def_EWILI2018_SchedulerSpec
open RamadgeWonham.Shared

namespace EWILI2018
theorem figure5_table2_replay :
    (figure5KernelTrace.take 8).filterMap schedulerSpecView = table2Events ∧
    (∀ k : Fin 7,
      schedulerSpec.run (table2Events.take (k.val + 1)) = some (table2States[k])) ∧
    LinuxRV.monitor schedulerSpec schedulerStateEnum schedulerEventEnum table2Events =
      .error (7, schedulerStateEnum .running, schedulerEventEnum .scheduleEntry) ∧
    LinuxRV.monitor schedulerSpec schedulerStateEnum schedulerEventEnum
        (figure5KernelTrace.filterMap schedulerSpecView) =
      .error (7, schedulerStateEnum .running, schedulerEventEnum .scheduleEntry) := by sorry
end EWILI2018
