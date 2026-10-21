-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_claim_3_2_block_work
-- name    : CloudMWU.Bicriteria.claim_3_2_block_work
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T13:05:27.942462+00:00
-- url     : https://prove2.me/theorems/f095d2e3-843d-462a-83d9-2230166de690
-- title:
--   Claim 3.2 (work form), p. 12 — on a block of $m\ge\tilde s$ steps with a continuously busy user, Algorithm 1 does work $\ge (1-4\varepsilon)m$
-- statement:
--   Let $N\ge2$, $0<\varepsilon\le1/10$, $0<\eta<1/3$, let $h$ be a run of Algorithm 1 on nonnegative loads, and let $\tilde s=\ln(N/\varepsilon)/(\varepsilon c)$ with $c=\varepsilon\eta/(4N)$. If $m\ge\tilde s$ and some user $i_0$ has a non-empty queue at every time $\tau\in[r,r+m]$, then the total work done by Algorithm 1 during the block $[r,r+m)$ is at least $(1-4\varepsilon)m$:
--   $$\sum_{\tau=r}^{r+m-1}\sum_i w_\tau(i)\ \ge\ (1-4\varepsilon)\,m .$$
--
--   This is the per-block conclusion of Claim 3.2 (the inequality $\sum_{t\in L}\sum_i w_t(i)\ge(1-4\varepsilon)|L|$ in its proof, Appendix B.2), stated for full blocks in which Claim 3.1 provides a busy user. The paper derives it from the count $|B'|\le 4\varepsilon\tilde s$ of low-utilization steps together with the observation that $h_t(i)=w_t(i)$ for active users. In the model (and in the formalization) an active user only has $Q_t(i)>0$, so it may complete less than $h_t(i)$ at time $t$; the statement nevertheless holds, because such a user empties its queue and is inactive at $t+1$, so the shortfall is controlled by the allocation held by inactive users, which the quantitative form of Lemma 1 bounds over the block.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 12, Claim 3.2, and its proof in Appendix B.2, p. 29 (the display $\sum_{t\in L}\sum_i w_t(i)\ge(1-4\varepsilon)|L|$)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem claim_3_2_block_work (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h)
    (r m : ℕ) (hm : sTilde N ε η ≤ (m : ℝ))
    (i₀ : Fin N) (hbusy : ∀ τ ∈ Icc r (r + m), 0 < runQueue h L τ i₀) :
    (1 - 4 * ε) * (m : ℝ)
      ≤ ∑ τ ∈ Ico r (r + m), ∑ i, work (fun s => h s i) (fun s => L s i) τ := by sorry

end CloudMWU.Bicriteria
