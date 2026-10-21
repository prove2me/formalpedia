-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_proposition_2_weak_duality
-- name    : CloudMWU.Bicriteria.proposition_2_weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:37.416626+00:00
-- url     : https://prove2.me/theorems/beedd34f-9cab-48d8-a465-53eac561790f
-- title:
--   Proposition 2, p. 11 — the bound v_{P_ε} ≤ Σ_{s≤t}Σ_i L_s(i) + (1 − ε)(T − t) (weak duality, the half used in the proof of Theorem 3)
-- statement:
--   Let $0 < \varepsilon < 1$, let $L$ be a nonnegative load sequence for $N$ users, and let $h^*$ be any sequence of $(1-\varepsilon)$-allocations, i.e. $h^*_t(i) \ge 0$ and $\sum_i h^*_t(i) \le 1 - \varepsilon$ at every step. Then for all times $s \le T$,
--
--   $$\mathrm{work}_{h^*}(T) \;\le\; \sum_{\tau=1}^{s} \sum_i L_\tau(i) \;+\; (1 - \varepsilon)(T - s),$$
--
--   where $\mathrm{work}_{h^*}(T)$ is the total work that $h^*$ completes in the first $T$ steps.
--
--   This is the half $v_{P_\varepsilon} \le \min_{0 \le s \le T}\big(\sum_{\tau=1}^{s}\sum_i L_\tau(i) + (1-\varepsilon)(T-s)\big)$ of Proposition 2, obtained in the paper by weak duality for the dual solution with $\gamma_t = 1, \beta_t = 0$ up to $s$ and $\gamma_t = 0, \beta_t = 1$ afterwards: up to time $s$ no allocation can complete more than the load that has arrived, and afterwards it completes at most $1 - \varepsilon$ per step. It bounds the offline benchmark in the proof of Theorem 3.
--
--   **Formalization Note** The statement is about the work of an allocation sequence in the queueing model, rather than about the value $v_{P_\varepsilon}$ of the LP $(P_\varepsilon)$; the work of every allocation sequence is a feasible point of $(P_\varepsilon)$, so this is the inequality the proof of Theorem 3 uses. Time is 0-based and queues start empty.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 11, Proposition 2 (the ≤ half; proof in Appendix B.1, p. 27, 'Consider the dual solution … Then, by weak duality')

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

namespace CloudMWU.Bicriteria

open Finset

theorem proposition_2_weak_duality (N : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (hstar : ℕ → Fin N → ℝ) (hstar_alloc : IsAllocSeq (1 - ε) hstar)
    (s t : ℕ) (hst : s ≤ t) :
    totalWork hstar L t ≤ totalLoad L s + (1 - ε) * ((t : ℝ) - (s : ℝ)) := by sorry

end CloudMWU.Bicriteria
