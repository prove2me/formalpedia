-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_theorem_1
-- name    : CloudMWU.Bicriteria.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:21.657856+00:00
-- url     : https://prove2.me/theorems/e99f44b8-da08-4a71-ac21-513e6cf7b4ad
-- title:
--   Theorem 1 (explicit constants of p. 10) — Algorithm 1 does ≥ (1−4ε)·(any offline dynamic work) − 2000N/(ε²η)·ln(N/ε), and meets every SLA up to (1−2ε) and β(i)p̃
-- statement:
--   Let $N \ge 2$ users share a resource of capacity 1. Let $0 < \varepsilon \le 1/10$ and $0 < \eta < 1/3$ be the parameters of Algorithm 1, let the SLAs satisfy $\beta(i) \ge 2\varepsilon/N$ for every $i$ and $\sum_i \beta(i) \le 1$, let $L_1, L_2, \dots \in \mathbb R^N_{\ge 0}$ be any loads, and let $h$ be a run of Algorithm 1 on these loads. Write $\mathrm{work}_h(t) = \sum_i \sum_{\tau=1}^t w_\tau(i)$ for the total work an allocation sequence completes in the first $t$ steps, and put $\tilde p = \frac{32N^2}{\varepsilon^3\eta}\ln\frac{N}{\varepsilon}$.
--
--   1. **Approximate work maximization.** For every offline allocation sequence $h^*$ (with $h^*_t(i) \ge 0$ and $\sum_i h^*_t(i) \le 1$ at every step) and every time $t$,
--   $$\mathrm{work}_{\mathrm{alg}}(t) \;\ge\; (1 - 4\varepsilon)\,\mathrm{work}_{h^*}(t) - 2000\,\frac{N}{\varepsilon^2\eta}\ln\frac{N}{\varepsilon}.$$
--   2. **Approximate SLA satisfaction.** For every user $i$, every comparator allocation sequence $h'$ with $0 \le h'_t(i) \le \beta(i)$ at every step, and every time $t$,
--   $$\sum_{\tau=1}^{t} w_\tau(i) \;\ge\; (1 - 2\varepsilon) \sum_{\tau=1}^{t} w'_\tau(i) - \beta(i)\,\tilde p,$$
--   where $w'_\tau(i)$ is the work user $i$ completes under $h'$ on the same loads.
--
--   The algorithm only observes which queues are non-empty. Part 1 compares it with the best *dynamic* offline allocation, which knows every load in advance, and part 2 with a dedicated share $\beta(i)$ of the resource for every single user, simultaneously.
--
--   **Formalization Note** Part 1 is the form displayed on p. 10, $(1-4\varepsilon)\,\mathrm{work}_{h^*} - 2000\frac{N}{\varepsilon^2\eta}\ln(N/\varepsilon)$, which is what the paper proves for the algorithm parameter $\varepsilon$; the headline's $(1-\varepsilon)$ with an unspecified $O(N\varepsilon^{-2}\log(N/\varepsilon))$ corresponds to running the algorithm at $\varepsilon/4$, which would also change part 2. The constants are explicit and depend on $\eta$, which the headline hides in $O(\cdot)$. "An optimal offline sequence with $\sum_i h^*_t(i) = 1$" is replaced by every sequence with $\sum_i h^*_t(i) \le 1$; this is equivalent (cumulative work is monotone in the allocation, and the optimum is one such sequence) and avoids a supremum. In part 2 only user $i$'s coordinate of $h'$ affects $w'(i)$, so the comparator is a single sequence $a_t \in [0, \beta(i)]$. The horizon $T$ is not a parameter: loads form an infinite sequence and both bounds hold at every $t$. $\sum_i \beta(i) \le 1$ is the model's standing assumption (p. 3). Queues start empty; time is 0-based.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 5, Theorem 1 (explicit constants from p. 10: the display after Theorem 3 and p̃ of Theorem 4)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem theorem_1 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ i, 2 * ε / (N : ℝ) ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) :
    (∀ hstar : ℕ → Fin N → ℝ, IsAllocSeq 1 hstar → ∀ t : ℕ,
      (1 - 4 * ε) * totalWork hstar L t
          - 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε)
        ≤ totalWork h L t) ∧
    (∀ (i : Fin N) (a : ℕ → ℝ), (∀ t, 0 ≤ a t ∧ a t ≤ β i) → ∀ t : ℕ,
      (1 - 2 * ε) * cumWork a (fun τ => L τ i) t - β i * pTilde N ε η
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) t) := by sorry

end CloudMWU.Bicriteria
