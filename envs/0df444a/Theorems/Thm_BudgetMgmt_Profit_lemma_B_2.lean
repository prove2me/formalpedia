-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_lemma_B_2
-- name    : BudgetMgmt.Profit.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:34.728718+00:00
-- url     : https://prove2.me/theorems/6b538b42-5abf-4f50-99b9-7f8cf095463c
-- title:
--   Lemma B.2, p. ec 45 — I^T(τ₁) < I^R(r₁) ⇒ G^T₁(τ₁) < G^R₁(r₁)
-- statement:
--   In the symmetric correlated setting, for every reserve price $r_1\ge c$ and every threshold $\tau_1\ge c$ (in particular for $r_1\in S_1^R$ and $\tau_1\in S_1^T$),
--   $$I^T(\tau_1)<I^R(r_1)\ \Longrightarrow\ G_1^T(\tau_1)<G_1^R(r_1),$$
--   where $I^\pi$ is the expected number of items sold and $G_1^\pi$ one buyer's expected expenditure when all buyers use the same parameter.
--
--   This is property (i) of the sufficient condition for dominance (p. ec 44) for the pair reserve pricing / thresholding: selling more items, reserve pricing also extracts more expenditure.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - generalization: r₁ ∈ S^R₁ and τ₁ ∈ S^T₁ → every r₁ ≥ c and τ₁ ≥ c; reason: S^R₁ and S^T₁ are contained in [c, ∞); the proof uses only r₁ ≥ c and the monotonicity of G^T₁ on [c, sup X₁]
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. ec 45, Lemma B.2

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Lemma B.2, p. ec 45: for reserve prices `r₁ ≥ c` and thresholds `τ₁ ≥ c`,
`I^T(τ₁) < I^R(r₁) ⇒ G^T₁(τ₁) < G^R₁(r₁)` (stated for every `r₁, τ₁ ≥ c`, which contains
`S^R₁ × S^T₁`). -/
theorem lemma_B_2 {n : ℕ} [NeZero n] (P : SymInstance n) (r τ : ℝ) (hr : P.c ≤ r)
    (hτ : P.c ≤ τ)
    (hI : itemsSold P .thresholding (sym τ) < itemsSold P .reserve (sym r)) :
    G1 P .thresholding τ < G1 P .reserve r := by sorry

end BudgetMgmt.Profit
