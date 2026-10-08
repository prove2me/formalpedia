-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_revenue_le_sum_price_mul_prob
-- name    : CHMSPricing.UnitDemand.revenue_le_sum_price_mul_prob
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:29:23.735574+00:00
-- url     : https://prove2.me/theorems/0752e33d-0bee-41a2-a27e-da570e22a0ae
-- title:
--   Lemma 2 (regular part), p. 5 — the revenue of a truthful mechanism is at most $\sum_i p^M_i q^M_i$
-- statement:
--   Consider a single-parameter instance with independent values $v_i \sim F_i$, each $F_i$ regular, and any set system $\mathcal J$. Let $M$ be a truthful mechanism, let $q^M_i$ be the probability (over $v_1,\dots,v_n$) that $M$ allocates to agent $i$, and let $p^M_i = F_i^{-1}(1 - q^M_i)$, the point of the support with $F_i(p^M_i) = 1 - q^M_i$. Then
--   $$\mathcal R^M \le \sum_i p^M_i q^M_i.$$
--
--   Applied to the instance with copies, this bounds the optimal revenue by a sum of single-agent posted-price revenues, the quantity the order-oblivious prices of Theorem 13 are compared with.
--
--   **Formalization Note** Only the first (regular) paragraph of Lemma 2 is stated; the second paragraph, about non-regular distributions and pairs of prices, is out of scope. The inverse distribution function is not defined: the prices $p^M_i$ are arguments, tied to $q^M_i$ by the hypothesis $p^M_i \in [\underline v_i, \overline v_i]$ and $F_i(p^M_i) = 1 - q^M_i$; such a point exists and is unique since $F_i$ is continuous and strictly increasing on the support. Regularity is assumed as in the paper.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, Lemma 2, first paragraph (restated p. 13, App. A)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_Mechanism

namespace CHMSPricing.UnitDemand

/-- Lemma 2 (regular part), p. 5: if every `Fᵢ` is regular, the revenue of every truthful
mechanism `M` is at most `∑ᵢ p^M_i q^M_i`, where `q^M_i` is the probability that `M` serves
agent `i` and `p^M_i = Fᵢ⁻¹(1 − q^M_i)` (the point of the support with `Fᵢ(p^M_i) = 1 − q^M_i`). -/
theorem revenue_le_sum_price_mul_prob {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (𝒥 : SetSystem ι)
    (M : Mechanism ι) (hM : IsTruthful D 𝒥 M) (pM : ι → ℝ)
    (hpM : ∀ i, pM i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (pM i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, pM i * servProb D M i := by sorry

end CHMSPricing.UnitDemand
