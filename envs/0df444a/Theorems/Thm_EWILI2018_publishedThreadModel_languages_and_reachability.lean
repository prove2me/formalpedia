-- Prove2me | Theorems.Thm_EWILI2018_publishedThreadModel_languages_and_reachability
-- name    : EWILI2018.publishedThreadModel_languages_and_reachability
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-24T08:00:29.677685+00:00
-- url     : https://prove2.me/theorems/3d162660-d0d5-4582-9aab-c5db03e8ea0f
-- title:
--   Synchronous product run factorization and exact $20$-state reachability
-- statement:
--   Establishes the run factorization and exact reachable state space of the synchronized four-automaton thread model $\mathcal{M}$ (`publishedThreadModel`):
--
--   1. For every finite trace $w \in \Sigma_{\mathrm{ker}}^*$ and product state $q = (q_1, q_2, q_3, q_4)$, $\hat{\delta}_{\mathcal{M}}(w, q_0) = q$ iff each filtered projection $P_j(w)$ drives component $\mathcal{G}_j$ from $q_{0,j}$ to $q_j$.
--   2. Every state $q_p \in Q_{\mathrm{spec}}$ of Figure 4 is reachable in `schedulerSpec`.
--   3. In the $28$-state product $Q = Q_1 \times Q_2 \times Q_3 \times Q_4$, a state $q = (q_1, q_2, q_3, q_4)$ is reachable from $q_0$ if and only if
--
--   $$\bigl(q_2 = \mathsf{runnable} \implies q_4 \notin \{\mathsf{sleepable}, \mathsf{preemptionSleepable}, \mathsf{suspending}\}\bigr) \;\land\; \bigl(q_2 = \mathsf{sleepable} \implies q_4 \neq \mathsf{preemptionToRunnable}\bigr).$$
--
--   This invariant cuts out the exact $20$ reachable states of $\mathcal{M}$ needed to establish supervisory nonblocking.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §§3 and 4.2, Figs. 3–4, pp. 3–5. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=4

import Definitions.Def_EWILI2018_SchedulerSpec
open RamadgeWonham.Shared

namespace EWILI2018
theorem publishedThreadModel_languages_and_reachability :
    (∀ (w : List KernelEvent) (q : ThreadModelState),
      publishedThreadModel.run w = some q ↔
        needReschedGen.run (w.filterMap needReschedView) = some q.1 ∧
        sleepRunGen.run (w.filterMap sleepRunView) = some q.2.1 ∧
        schedContextGen.run (w.filterMap schedContextView) = some q.2.2.1 ∧
        schedulerSpec.run (w.filterMap schedulerSpecView) = some q.2.2.2) ∧
    (∀ qp : SchedulerSpecState, ∃ u : List SchedulerSpecEvent, schedulerSpec.run u = some qp) ∧
    (∀ q : ThreadModelState,
      (∃ w : List KernelEvent, publishedThreadModel.run w = some q) ↔
        (q.2.1 = .runnable →
          q.2.2.2 ≠ .sleepable ∧ q.2.2.2 ≠ .preemptionSleepable ∧ q.2.2.2 ≠ .suspending) ∧
        (q.2.1 = .sleepable → q.2.2.2 ≠ .preemptionToRunnable)) := by sorry
end EWILI2018
