-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_lemma_B_3
-- name    : BudgetMgmt.Profit.lemma_B_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:24.757427+00:00
-- url     : https://prove2.me/theorems/92513b94-9dd1-426d-862b-fc4b85446179
-- title:
--   Lemma B.3, p. ec 46 — I^S(µ₁) < I^T(τ₁) ⇒ G^S₁(µ₁) < G^T₁(τ₁)
-- statement:
--   In the symmetric correlated setting, for every threshold $\tau_1\ge c$ and every shading parameter $\mu_1\ge0$ (in particular for $\tau_1\in S_1^T$ and $\mu_1\in S_1^S$),
--   $$I^S(\mu_1)<I^T(\tau_1)\ \Longrightarrow\ G_1^S(\mu_1)<G_1^T(\tau_1).$$
--
--   Together with the equal maximal expenditures and items sold of the two mechanisms (property (ii), p. ec 44), this yields "Thresholding $\ge$ Bid Shading" for profit.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - generalization: τ₁ ∈ S^T₁ and µ₁ ∈ S^S₁ → every τ₁ ≥ c and µ₁ ≥ 0; reason: S^T₁ ⊆ [c, ∞) and S^S₁ ⊆ [0, ∞)
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. ec 46, Lemma B.3

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Lemma B.3, p. ec 46: for thresholds `τ₁ ≥ c` and shading parameters `μ₁ ≥ 0`,
`I^S(μ₁) < I^T(τ₁) ⇒ G^S₁(μ₁) < G^T₁(τ₁)` (stated for every `τ₁ ≥ c`, `μ₁ ≥ 0`, which contains
`S^T₁ × S^S₁`). -/
theorem lemma_B_3 {n : ℕ} [NeZero n] (P : SymInstance n) (τ μ : ℝ) (hτ : P.c ≤ τ)
    (hμ : 0 ≤ μ)
    (hI : itemsSold P .shading (sym μ) < itemsSold P .thresholding (sym τ)) :
    G1 P .shading μ < G1 P .thresholding τ := by sorry

end BudgetMgmt.Profit
