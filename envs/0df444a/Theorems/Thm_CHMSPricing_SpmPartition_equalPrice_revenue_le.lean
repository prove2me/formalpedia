-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_equalPrice_revenue_le
-- name    : CHMSPricing.SpmPartition.equalPrice_revenue_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:44:06.899987+00:00
-- url     : https://prove2.me/theorems/138e6aec-1a25-4158-9115-5bfc526974d0
-- title:
--   Lemma 20, p. 15 — the single-unit SPM revenue is at least that of the SPM with all prices equal to the average price p
-- statement:
--   Let $q_0,\dots,q_{n-1}\in[0,1]$ be acceptance probabilities and $p_0\ge p_1\ge\cdots\ge p_{n-1}$ prices, indexed by position in a single-unit offer order (decreasing prices), and let $c_k=\prod_{j<k}(1-q_j)$. Let $p$ be the price satisfying equation (2),
--
--   $$
--   \sum_k p_kq_k=p\sum_k q_k .
--   $$
--
--   Then
--
--   $$
--   p\sum_k c_kq_k\;\le\;\sum_k c_k\,p_k\,q_k .
--   $$
--
--   The right-hand side is the revenue $\mathcal R^{\mathcal S}$ of the single-unit SPM, and the left-hand side is $\mathcal R^{\mathcal S}_{\rm eq}$, the revenue of an SPM with the same acceptance probabilities in which every price equals $p$. The lemma reduces the single-unit analysis to the equal-price case.
--
--   **Formalization Note** On the page $\mathcal R^{\mathcal S}_{\rm eq}$ is the revenue under hypothetical distributions $G_i$ with the same $q_i$ and all prices equal to $p$; by the single-unit revenue formula that revenue is $p\sum_k c_kq_k$, and the statement compares these two quantities directly. The decreasing order of prices (antitone in position) is essential and kept as a hypothesis: the page's proof uses it to get a single sign change of $\delta_i=q_i(p_i-p)$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 15, App. C.2, Lemma 20 (with eq. (2), p. 14, and the definition of R^S_eq, p. 15)

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_Spm

namespace CHMSPricing.SpmPartition

theorem equalPrice_revenue_le {n : ℕ} (q pr : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hpr : Antitone pr)
    (pbar : ℝ) (h2 : ∑ i, pr i * q i = pbar * ∑ i, q i) :
    pbar * ∑ i, oneUnitOfferProb q i * q i ≤ ∑ i, oneUnitOfferProb q i * pr i * q i := by sorry

end CHMSPricing.SpmPartition
