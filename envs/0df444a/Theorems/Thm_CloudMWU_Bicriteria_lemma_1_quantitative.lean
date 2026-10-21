-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_lemma_1_quantitative
-- name    : CloudMWU.Bicriteria.lemma_1_quantitative
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T13:05:11.450976+00:00
-- url     : https://prove2.me/theorems/dbc50738-f887-491f-a7e0-14ee7321d951
-- title:
--   Quantitative form of the proof of Lemma 1 — an active user's allocation grows in proportion to the inactive mass $\sum_{j\in B_t}h_t(j)$
-- statement:
--   Let $N\ge2$, $0<\varepsilon\le 1/10$, $0<\eta<1/3$, $\lambda=\varepsilon^2/(8N)$, let $h$ be a run of Algorithm 1 on nonnegative loads, and let $b_t=\sum_{j\in B_t}h_t(j)$ be the allocation held by the inactive users $B_t=[N]\setminus A_t$ at time $t$. Then for every active user $i\in A_t$,
--   $$h_t(i)\ \le\ h_{t+1}(i)\Big(e^{\lambda\eta}-\big(e^{\lambda\eta}-e^{-\eta}\big)\big(b_t-e^{\eta(1+\lambda)}\varepsilon\big)\Big).$$
--
--   This is the computation in the proof of Lemma 1, part 1 (Appendix B.2), kept quantitative: there, for $i\in A_t$, $h_{t+1}(i)\ge h_t(i)\,(1-\frac{\varepsilon}{N}|S_{t+1}|)\,/\,(e^{-\eta}\sum_{j\notin S_{t+1}}\hat h_{t+1}(j))$ and $e^{-\eta}\sum_{j\notin S_{t+1}}\hat h_{t+1}(j)\le e^{\lambda\eta}\sum_{j\notin S_{t+1}}h_t(j)-(e^{\lambda\eta}-e^{-\eta})\sum_{j\in B_t\setminus S_{t+1}}h_t(j)$. Instead of bounding $\sum_{j\in B_t\setminus S_{t+1}}h_t(j)$ below by $\varepsilon/N$, we bound it below by $b_t-e^{\eta(1+\lambda)}\varepsilon$, using that every $j\in B_t\cap S_{t+1}$ has $h_t(j)\le e^{\eta(1+\lambda)}\varepsilon/N$ (as in the proof of Lemma 2). The bound says that a busy user gains multiplicatively in proportion to the total resource left idle by inactive users; it is used to bound the total idle allocation over a block in the proof of Claim 3.2.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Appendix B.2, p. 28, proof of Lemma 1 part 1 (first case), combined with the bound $h_t(j)\le e^{\eta(1+\lambda)}\varepsilon/N$ for $j\in S_{t+1}$ from the proof of Lemma 2, Appendix B.3, p. 29

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem lemma_1_quantitative (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3) (β : Fin N → ℝ)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t,
      h t i ≤ h (t + 1) i * (Real.exp (lam N ε * η)
        - (Real.exp (lam N ε * η) - Real.exp (-η))
          * (∑ j ∈ (active h L t)ᶜ, h t j - Real.exp (η * (1 + lam N ε)) * ε)) := by sorry

end CloudMWU.Bicriteria
