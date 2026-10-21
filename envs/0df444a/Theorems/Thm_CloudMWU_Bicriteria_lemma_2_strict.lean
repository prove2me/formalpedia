-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_lemma_2_strict
-- name    : CloudMWU.Bicriteria.lemma_2_strict
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-20T13:05:10.637189+00:00
-- url     : https://prove2.me/theorems/e1068f37-f670-4724-a60f-6e6bf9b95a5b
-- title:
--   Lemma 2 under the SLA bound of Theorem 4 — $\beta(j) > e^{\eta(1+\lambda)}\varepsilon/N$ suffices for the $(1+c')$ boost on $A^1_t$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta<1/3$, $\lambda=\varepsilon^2/(8N)$ and $c'=\varepsilon\eta\lambda/(2N)$. Suppose the SLAs satisfy $\sum_j\beta(j)\le 1$ and $\beta(j)>e^{\eta(1+\lambda)}\varepsilon/N$ for every user $j$, and let $h$ be a run of Algorithm 1 on nonnegative loads. Then for every time $t$ and every active user $i\in A_t$ with $h_t(i)<\beta(i)$ (i.e. $i\in A^1_t$),
--   $$h_{t+1}(i)\ \ge\ h_t(i)\,(1+c').$$
--
--   This is Lemma 2 of the paper with its hypothesis $\beta(j)\ge 2\varepsilon/N$ replaced by the SLA lower bound $\beta(j)> e^{\eta(1+\lambda)}\varepsilon/N$ assumed in Theorem 4. The paper's proof of Lemma 2 (Appendix B.3) uses the hypothesis only through the inequality $h_t(j)\le e^{\eta(1+\lambda)}\varepsilon/N<\beta(j)$ for $j\in S_{t+1}$, so it proves this form verbatim; this is the form needed to apply Lemma 2 inside the proof of Theorem 4.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 13, Lemma 2 (proof in Appendix B.3, p. 29), with the SLA hypothesis of Theorem 4 (p. 10)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem lemma_2_strict (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j)
    (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (t : ℕ) :
    ∀ i ∈ active h L t, h t i < β i → h t i * (1 + cLem2 N ε η) ≤ h (t + 1) i := by sorry

end CloudMWU.Bicriteria
