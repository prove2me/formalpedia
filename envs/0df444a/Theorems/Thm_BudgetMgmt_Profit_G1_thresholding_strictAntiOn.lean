-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_G1_thresholding_strictAntiOn
-- name    : BudgetMgmt.Profit.G1_thresholding_strictAntiOn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:21.565558+00:00
-- url     : https://prove2.me/theorems/529e1042-36a7-478d-9fc0-cebd468bf714
-- title:
--   Proof of Proposition 4.1 (thresholding), p. ec 39 — G^T₁(τ₁) strictly decreases on [c, sup X₁]
-- statement:
--   In the symmetric correlated setting, let every buyer use the same threshold $\tau_1$ under the thresholding mechanism, and let $G_1^{T}(\tau_1)$ be one buyer's expected expenditure over the horizon. Then
--   $$G_1^T(\tau_1)=T\,\mathbb E\big[(d_1\vee c)\,\mathbf 1\{x_1\ge\tau_1\vee d_1\}\big],\qquad d_1=\max_{i\ne1:\,x_i\ge\tau_1}x_i,$$
--   is strictly decreasing in $\tau_1$ on $\{\tau_1: c\le\tau_1\le\sup X_1\}$.
--
--   Every parameter space $S_1=[c,\bar\tau]$ chosen in the proof of Theorem 3.2 lies in this set, so this is the monotonicity that makes the one-variable complementarity problem of Proposition 4.1 uniquely solvable for thresholding.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - generalization: G^T₁ strictly decreases for τ₁ ∈ S₁, the parameter space determined in Theorem 3.2 → strict decrease on {τ₁ : c ≤ τ₁, τ₁ ≤ v̄}; reason: this set contains every S₁ = [c, τ̄] of Theorem 3.2
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. ec 39, proof of Proposition 4.1 (Thresholding)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Proof of Proposition 4.1 (thresholding), p. ec 39: at symmetric profiles, one buyer's expected
expenditure under thresholding, `G^T₁(τ₁)`, strictly decreases in `τ₁` over `[c, sup X₁]` (every
parameter space `S₁ = [c, τ̄]` of Theorem 3.2 lies in this set). -/
theorem G1_thresholding_strictAntiOn {n : ℕ} [NeZero n] (P : SymInstance n) :
    StrictAntiOn (G1 P .thresholding) {τ | P.c ≤ τ ∧ ENNReal.ofReal τ ≤ P.vbar} := by sorry

end BudgetMgmt.Profit
