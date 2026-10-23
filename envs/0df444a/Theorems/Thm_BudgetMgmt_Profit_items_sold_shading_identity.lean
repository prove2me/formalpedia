-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_items_sold_shading_identity
-- name    : BudgetMgmt.Profit.items_sold_shading_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:33.067189+00:00
-- url     : https://prove2.me/theorems/7fddf8e3-0b18-4cbe-b9dd-4eba901c7499
-- title:
--   Proofs of Lemmas B.2, B.3, pp. ec 45–46 — I^T(τ₁) = T(1−F(τ₁1⃗)), I^R(r₁) = T(1−F(r₁1⃗)), I^S(µ₁) = T(1−F((1+µ₁)c1⃗)), G^S₁(µ₁) = G^R₁((1+µ₁)c)/(1+µ₁)
-- statement:
--   In the symmetric correlated setting, with $F$ the joint CDF of the values and every buyer using the same parameter, the expected numbers of items sold are
--   $$I^T(\tau_1)=T\big(1-F(\tau_1\vec1)\big),\qquad I^R(r_1)=T\big(1-F(r_1\vec1)\big),\qquad I^S(\mu_1)=T\big(1-F((1+\mu_1)c\vec1)\big)$$
--   for all $\tau_1,r_1,\mu_1\ge0$, and one buyer's expenditure under bid shading equals a rescaled expenditure under reserve pricing at the reserve $(1+\mu_1)c$:
--   $$G_1^S(\mu_1)=\frac{1}{1+\mu_1}\,G_1^R\big((1+\mu_1)c\big)\qquad(\mu_1\ge0).$$
--
--   These identities turn the comparisons of Lemmas B.2 and B.3 into comparisons of parameters: fewer items sold means a higher symmetric parameter.
--
--   **Formalization Note** The paper sets $T=1$ (p. ec 44); the factor $T$ is kept. $G_1^R((1+\mu_1)c)$ is the Table 1 expenditure at a symmetric profile, which need not lie in reserve pricing's restricted space.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - generalization: the identities are used for τ₁ ∈ S^T₁, r₁ ∈ S^R₁, µ₁ ∈ S^S₁ → they are stated for all τ₁, r₁, µ₁ ≥ 0; reason: these sets contain the parameter spaces
--   - encoding: T = 1 without loss of generality (p. ec 44) → the factor T is kept in I and G; reason: I and G carry the factor T by their definitions on pp. 6–7
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), pp. ec 45–46, proofs of Lemma B.2 and Lemma B.3, (B-21), (B-22)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Proofs of Lemmas B.2 and B.3, pp. ec 45–46: at symmetric profiles the expected number of items
sold is `I^T(τ₁) = T(1 − F(τ₁1⃗))`, `I^R(r₁) = T(1 − F(r₁1⃗))`, `I^S(μ₁) = T(1 − F((1 + μ₁)c1⃗))`, and
by (B-21), (B-22) `G^S₁(μ₁) = G^R₁((1 + μ₁)c)/(1 + μ₁)`. -/
theorem items_sold_shading_identity {n : ℕ} [NeZero n] (P : SymInstance n) :
    (∀ τ : ℝ, 0 ≤ τ → itemsSold P .thresholding (sym τ) = P.T * (1 - cdf P (sym τ))) ∧
    (∀ r : ℝ, 0 ≤ r → itemsSold P .reserve (sym r) = P.T * (1 - cdf P (sym r))) ∧
    (∀ μ : ℝ, 0 ≤ μ →
      itemsSold P .shading (sym μ) = P.T * (1 - cdf P (sym ((1 + μ) * P.c)))) ∧
    (∀ μ : ℝ, 0 ≤ μ → G1 P .shading μ = G1 P .reserve ((1 + μ) * P.c) / (1 + μ)) := by sorry

end BudgetMgmt.Profit
