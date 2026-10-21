-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_theorem_3
-- name    : CloudMWU.Bicriteria.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:24.412951+00:00
-- url     : https://prove2.me/theorems/3ccdc239-9d7d-416b-bcb2-9c2d7689acb7
-- title:
--   Theorem 3, p. 10 — against any (1−4ε)-allocation sequence, Algorithm 1 loses ≤ 8N/(ε²η)·ln(N/ε) work at every t (with the integer-block slack +2)
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$, let $\beta$ be any SLA vector, $L$ a nonnegative load sequence and $h$ a run of Algorithm 1. Let $h^*$ be any offline sequence of $(1 - 4\varepsilon)$-allocations: $h^*_t(i) \ge 0$ and $\sum_i h^*_t(i) \le 1 - 4\varepsilon$ at every step. Then at every time $t$,
--
--   $$\mathrm{work}_{h^*}(t) - \mathrm{work}_{\mathrm{alg}}(t) \;\le\; \frac{8N}{\varepsilon^2\eta}\ln\frac{N}{\varepsilon} + 2,$$
--
--   where $\mathrm{work}_{h}(t) = \sum_i \sum_{\tau=1}^{t} w_\tau(i)$ is the total work an allocation sequence completes in the first $t$ steps.
--
--   The benchmark is *dynamic*: $h^*$ may change arbitrarily over time and knows all loads in advance. The theorem says that Algorithm 1, which only observes which queues are non-empty, nearly matches every such benchmark that uses slightly less of the resource.
--
--   **Formalization Note** The additive "$+2$" is a disclosed correction: the paper's $\tilde s$ is real, the proof's blocks have integer length $\lceil \tilde s\rceil$, and the argument then gives $2\lceil\tilde s\rceil \le 2\tilde s + 2$ with $2\tilde s = 8N/(\varepsilon^2\eta)\ln(N/\varepsilon)$. The paper's "$\eta > 0$" is replaced by Algorithm 1's input $0 < \eta < 1/3$, which Lemma 1 needs. "The optimal offline sequence" is replaced by every sequence of $(1-4\varepsilon)$-allocations, which is equivalent (the optimum is one of them and every one does at most the optimum's work) and avoids a supremum. No horizon $T$: the bound holds at every $t$ for an infinite load sequence. Queues start empty; time is 0-based.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 10, Theorem 3 (proof pp. 11–12)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem theorem_3 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (hstar : ℕ → Fin N → ℝ) (hstar_alloc : IsAllocSeq (1 - 4 * ε) hstar) (t : ℕ) :
    totalWork hstar L t - totalWork h L t
      ≤ 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) + 2 := by sorry

end CloudMWU.Bicriteria
