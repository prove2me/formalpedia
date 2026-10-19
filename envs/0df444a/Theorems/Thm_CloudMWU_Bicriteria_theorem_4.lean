-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_theorem_4
-- name    : CloudMWU.Bicriteria.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:32.19624+00:00
-- url     : https://prove2.me/theorems/ba868626-1a9e-4905-a5f9-0556b59b6c13
-- title:
--   Theorem 4, p. 10 — if β(j) > e^{η(1+λ)}ε/N, each user's work by time t + p̃ is ≥ that of the constant allocation (1 − 2ε)β(i) by time t (strict SLA bound)
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$, $\lambda = \varepsilon^2/(8N)$ and $\tilde p = \frac{32N^2}{\varepsilon^3\eta}\ln\frac{N}{\varepsilon}$. Let the SLAs satisfy $\beta(j) > e^{\eta(1+\lambda)}\varepsilon/N$ for every user $j$ and $\sum_j \beta(j) \le 1$, let $L$ be a nonnegative load sequence and $h$ a run of Algorithm 1. Fix a user $i$, and let $w'_\tau(i)$ be the work that user $i$ would complete with the constant allocation $h'_\tau(i) = (1 - 2\varepsilon)\beta(i)$ on the same loads. Then for every time $t$:
--
--   1. $$\sum_{\tau=1}^{t + \lceil\tilde p\rceil} w_\tau(i) \;\ge\; \sum_{\tau=1}^{t} w'_\tau(i);$$
--   2. $$\sum_{\tau=1}^{t} w_\tau(i) \;\ge\; \sum_{\tau=1}^{t} w'_\tau(i) - \beta(i)\,\tilde p.$$
--
--   Each user is therefore served, up to a delay of $\tilde p$ steps, at least as well as by a dedicated share of $(1-2\varepsilon)\beta(i)$ of the resource, although the algorithm never sees loads or queue lengths.
--
--   **Formalization Note** Four disclosed changes. (i) The SLA bound is **strict**, $\beta(j) > e^{\eta(1+\lambda)}\varepsilon/N$: the proof applies Lemma 2, whose argument needs $h_t(j) \le (\varepsilon/N)e^{\eta(1+\lambda)} < \beta(j)$. (ii) $0 < \eta < 1/3$ (Algorithm 1's input) instead of $\eta \le 1/3$. (iii) The paper's restriction $t \le T - \tilde p$ only keeps $t + \tilde p$ inside a finite horizon; loads here are an infinite sequence, so it is dropped. (iv) The window is $\lceil\tilde p\rceil$ steps, since time is discrete. Time is 0-based and queues start empty.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 10, Theorem 4 (proof p. 13)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem theorem_4 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j)
    (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (i : Fin N) (t : ℕ) :
    cumWork (fun _ => (1 - 2 * ε) * β i) (fun τ => L τ i) t
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) (t + ⌈pTilde N ε η⌉₊) ∧
    cumWork (fun _ => (1 - 2 * ε) * β i) (fun τ => L τ i) t - β i * pTilde N ε η
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) t := by sorry

end CloudMWU.Bicriteria
