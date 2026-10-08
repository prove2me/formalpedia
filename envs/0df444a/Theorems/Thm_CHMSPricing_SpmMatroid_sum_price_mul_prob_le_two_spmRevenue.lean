-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_sum_price_mul_prob_le_two_spmRevenue
-- name    : CHMSPricing.SpmMatroid.sum_price_mul_prob_le_two_spmRevenue
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:41:20.50498+00:00
-- url     : https://prove2.me/theorems/0ce7efdc-c738-45f1-a641-90d1109212e5
-- title:
--   §4.1, proof of Theorem 5, p. 7 — under a matroid, Σ_i p_i q_i ≤ 2·R^σ_p
-- statement:
--   Let $\mathcal J$ be a matroid on $[n]$ and let the values $v_i \sim F_i$ be independent. Let prices $p_i \in [\underline v_i, \overline v_i]$ have acceptance probabilities $q_i = 1 - F_i(p_i)$ with $\sum_{i \in T} q_i \le \operatorname{rank}(T)$ for every $T$, and let the ordering $\sigma$ approach the agents in decreasing order of price. Then
--
--   $$\sum_i p_i\, q_i \le 2\, \mathcal R^\sigma_{\mathbf p}.$$
--
--   This is the posted-price half of Theorem 5: no mechanism appears, only the rank condition on the acceptance probabilities.
--
--   **Formalization Note** Ties in "decreasing order of prices" are arbitrary: the statement holds for every ordering with $p_{\sigma(b)} \le p_{\sigma(a)}$ whenever $a \le b$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 7, §4.1, last line of the proof of Theorem 5

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Spm

namespace CHMSPricing.SpmMatroid

/-- §4.1, end of the proof of Theorem 5 (p. 7): under a matroid constraint, if the prices
`pᵢ ∈ [loᵢ, hiᵢ]` have acceptance probabilities `qᵢ = 1 − Fᵢ(pᵢ)` with `∑_{i ∈ T} qᵢ ≤ rank(T)`
for every `T`, and the agents are approached in decreasing order of price, then
`∑ᵢ pᵢ qᵢ ≤ 2 ℛ^σ_p`. -/
theorem sum_price_mul_prob_le_two_spmRevenue {n : ℕ} (D : Fin n → ValueDist)
    (J : SetSystem (Fin n)) (hJ : J.IsMatroid)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi)
    (hqr : ∀ T : Finset (Fin n), ∑ i ∈ T, (1 - (D i).cdf (p i)) ≤ (J.rank T : ℝ))
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a b, a ≤ b → p (σ b) ≤ p (σ a)) :
    ∑ i, p i * (1 - (D i).cdf (p i)) ≤ 2 * spmRevenue D J σ p := by sorry

end CHMSPricing.SpmMatroid
