-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_lemma_1
-- name    : CloudMWU.Bicriteria.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:28.750969+00:00
-- url     : https://prove2.me/theorems/cef3d90d-b1c3-4cd2-a442-4840998a3f77
-- title:
--   Lemma 1, p. 11 — active users gain a factor (1 + c) when utilization ≤ 1 − ε; A¹_t never loses, A²_t loses at most (1 − εc), c = εη/(4N)
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, $0 < \eta < 1/3$, let $\beta$ be any SLA vector and $L$ any nonnegative load sequence, and let $h$ be a run of Algorithm 1. Put $c = \varepsilon\eta/(4N)$. For every step $t$, with $A_t$ the active users, $A^1_t = \{i \in A_t : h_t(i) < \beta(i)\}$ and $A^2_t = A_t \setminus A^1_t$:
--
--   1. If $\sum_{j \in A_t} h_t(j) \le 1 - \varepsilon$, then every $i \in A_t$ satisfies
--   $$h_{t+1}(i) \ge h_t(i)(1 + c).$$
--   2. Every $i \in A^1_t$ satisfies $h_{t+1}(i) \ge h_t(i)$, and every $i \in A^2_t$ satisfies $h_{t+1}(i) \ge h_t(i)(1 - \varepsilon c)$.
--
--   The lemma quantifies the two effects of the multiplicative update: when the busy users hold little of the resource they all gain a fixed factor, and in general a busy user can lose only a small factor per step. It drives the counting argument of Claim 3.2 and hence Theorem 3.
--
--   **Formalization Note** Time is 0-based (`h t` is the paper's $h_{t+1}$). The paper's Algorithm 1 input $0 < \eta < 1/3$ is assumed. No condition on $\beta$ is needed.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 11, Lemma 1 (proof in Appendix B.2, pp. 27–28)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem lemma_1 (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    (∑ j ∈ active h L t, h t j ≤ 1 - ε →
      ∀ i ∈ active h L t, h t i * (1 + cLem1 N ε η) ≤ h (t + 1) i) ∧
    (∀ i ∈ active h L t, h t i < β i → h t i ≤ h (t + 1) i) ∧
    (∀ i ∈ active h L t, β i ≤ h t i → h t i * (1 - ε * cLem1 N ε η) ≤ h (t + 1) i) := by sorry

end CloudMWU.Bicriteria
