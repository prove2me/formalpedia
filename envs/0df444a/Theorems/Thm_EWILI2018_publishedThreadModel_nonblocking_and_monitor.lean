-- Prove2me | Theorems.Thm_EWILI2018_publishedThreadModel_nonblocking_and_monitor
-- name    : EWILI2018.publishedThreadModel_nonblocking_and_monitor
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T08:01:15.253423+00:00
-- url     : https://prove2.me/theorems/8a7e0195-e18c-4a95-bc7d-5eb6bdee9387
-- title:
--   Nonblocking supervisory product and modular table-monitor correctness
-- statement:
--   Establishes the main supervisory and runtime-verification properties of the synchronized EWILI 2018 thread model $\mathcal{M}$ (`publishedThreadModel`) over the $15$-event Table 1 alphabet $\Sigma_{\mathrm{ker}}$:
--
--   1. **Ramadge–Wonham nonblocking:** Every legal trace $w \in L(\mathcal{M})$ admits a finite continuation $u \in \Sigma_{\mathrm{ker}}^*$ returning all four components simultaneously to their marked safe states:
--
--   $$w \in L(\mathcal{M}) \implies \exists u \in \Sigma_{\mathrm{ker}}^*,\; w \cdot u \in L_m(\mathcal{M}).$$
--
--   2. **Modular acceptance of the generated table monitor:** The compiled $28 \times 15$ integer transition-table monitor `LinuxRV.monitor` accepts $w$ iff all four filtered projections $P_1(w), P_2(w), P_3(w), P_4(w)$ belong to the generated languages of `needReschedGen`, `sleepRunGen`, `schedContextGen`, and `schedulerSpec`.
--   3. **Component-level first-failure localization:** The monitor reports $(i, \sigma_Q(q), \sigma_{\Sigma}(e))$ iff $w = \mathrm{pre} \cdot [e] \cdot \mathrm{post}$ with $|\mathrm{pre}| = i$, $\hat{\delta}_{\mathcal{M}}(\mathrm{pre}, q_0) = q$, and at least one participating component has no defined transition from $q_j$ on $\pi_j(e)$.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §§3, 4.2 and 5, Figs. 3–4 and Table 1, pp. 3–5. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=4

import Definitions.Def_EWILI2018_SchedulerSpec
open RamadgeWonham.Shared

namespace EWILI2018
theorem publishedThreadModel_nonblocking_and_monitor (w : List KernelEvent) :
    (w ∈ publishedThreadModel.L → ∃ u : List KernelEvent, w ++ u ∈ publishedThreadModel.Lm) ∧
    ((∃ q, LinuxRV.monitor publishedThreadModel threadModelStateEnum kernelEventEnum w = .ok q) ↔
      w.filterMap needReschedView ∈ needReschedGen.L ∧
      w.filterMap sleepRunView ∈ sleepRunGen.L ∧
      w.filterMap schedContextView ∈ schedContextGen.L ∧
      w.filterMap schedulerSpecView ∈ schedulerSpec.L) ∧
    (∀ i q e,
      LinuxRV.monitor publishedThreadModel threadModelStateEnum kernelEventEnum w =
        .error (i, threadModelStateEnum q, kernelEventEnum e) ↔
      ∃ pre post, w = pre ++ e :: post ∧ pre.length = i ∧
        publishedThreadModel.run pre = some q ∧
        ((∃ a, needReschedView e = some a ∧ needReschedGen.δ a q.1 = none) ∨
         (∃ a, sleepRunView e = some a ∧ sleepRunGen.δ a q.2.1 = none) ∨
         (∃ a, schedContextView e = some a ∧ schedContextGen.δ a q.2.2.1 = none) ∨
         (∃ a, schedulerSpecView e = some a ∧ schedulerSpec.δ a q.2.2.2 = none))) := by sorry
end EWILI2018
