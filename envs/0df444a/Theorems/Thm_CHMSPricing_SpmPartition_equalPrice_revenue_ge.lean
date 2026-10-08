-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_equalPrice_revenue_ge
-- name    : CHMSPricing.SpmPartition.equalPrice_revenue_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:43:58.633456+00:00
-- url     : https://prove2.me/theorems/bffdf7fe-4cd9-4b5c-8339-556075c02d7c
-- title:
--   Display (3), p. 15 — with Σ q_i = s ≤ 1, the equal-price single-unit SPM earns at least (1 − 1/e)·p·s
-- statement:
--   Let $n\ge1$, let $q_0,\dots,q_{n-1}\in[0,1]$ with $s=\sum_k q_k\le1$, let $c_k=\prod_{j<k}(1-q_j)$, and let $p\ge0$. The revenue of the single-unit SPM in which every agent faces the price $p$ is $\mathcal R^{\mathcal S}_{\rm eq}=p\sum_kc_kq_k$, and
--
--   $$
--   \begin{aligned}
--   p\sum_k c_kq_k&=p\Big(1-\prod_{k}(1-q_k)\Big)\\
--   &\ge p\Big(1-\big(1-\tfrac sn\big)^n\Big)\\
--   &\ge\big(1-\tfrac1e\big)\,p\,s .
--   \end{aligned}
--   $$
--
--   The first line says that the equal-price SPM earns $p$ times the probability that some agent is served; the second (the paper's display (3)) that this probability is smallest when the $q_k$ are equal; the third is the elementary bound that turns it into the factor $1-1/e$. Together with Lemma 20 this proves the single-unit case (Theorem 21).
--
--   **Formalization Note** The three relations are stated as a conjunction, each multiplied by $p\ge0$ as on the page; $p$ is the price of equation (2), which is non-negative because all prices lie in supports contained in $[0,\infty)$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 15, App. C.2, proof of Theorem 21, the display ending in (3) and the bound (1 − 1/e)ps

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem equalPrice_revenue_ge {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hs : ∑ i, q i ≤ 1) (pbar : ℝ) (hpbar : 0 ≤ pbar) :
    pbar * ∑ i, oneUnitOfferProb q i * q i = pbar * (1 - ∏ i, (1 - q i)) ∧
    pbar * (1 - (1 - (∑ i, q i) / n) ^ n) ≤ pbar * (1 - ∏ i, (1 - q i)) ∧
    (1 - 1 / Real.exp 1) * pbar * (∑ i, q i) ≤ pbar * (1 - (1 - (∑ i, q i) / n) ^ n) := by sorry

end CHMSPricing.SpmPartition
