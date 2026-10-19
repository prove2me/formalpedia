-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_lemma_2
-- name    : CloudMWU.Bicriteria.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:24.155215+00:00
-- url     : https://prove2.me/theorems/4ace0f39-c04d-4ecf-a0d2-e12f06d4a05f
-- title:
--   Lemma 2, p. 13 — if β(j) ≥ 2ε/N for all users, every i ∈ A¹_t gains h_{t+1}(i) ≥ h_t(i)(1 + c′), c′ = εηλ/(2N)
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$ and $\lambda = \varepsilon^2/(8N)$. Let the SLAs satisfy $\beta(j) \ge 2\varepsilon/N$ for every user $j$ and $\sum_j \beta(j) \le 1$, let $L$ be a nonnegative load sequence and $h$ a run of Algorithm 1. Then for every step $t$ and every active user $i$ below its SLA ($i \in A^1_t$, i.e. $i \in A_t$ and $h_t(i) < \beta(i)$),
--
--   $$h_{t+1}(i) \;\ge\; h_t(i)\,(1 + c'), \qquad c' = \frac{\varepsilon\eta\lambda}{2N}.$$
--
--   A busy user below its SLA thus grows geometrically until it reaches its SLA; this is the engine of the SLA guarantee, Theorem 4.
--
--   **Formalization Note** The paper's proof uses $\sum_j \beta(j) = 1$; the model only assumes $\sum_j \beta(j) \le 1$ (p. 3), which suffices for the argument, so the standing assumption $\sum_j \beta(j) \le 1$ is used. The paper's $\eta \le 1/3$ is replaced by Algorithm 1's input $0 < \eta < 1/3$. Time is 0-based.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 13, Lemma 2 (proof in Appendix B.3, pp. 29–30)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem lemma_2 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, 2 * ε / (N : ℝ) ≤ β j) (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t, h t i < β i → h t i * (1 + cLem2 N ε η) ≤ h (t + 1) i := by sorry

end CloudMWU.Bicriteria
