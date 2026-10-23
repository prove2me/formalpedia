-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_G1_shading_strictAntiOn
-- name    : BudgetMgmt.Profit.G1_shading_strictAntiOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:23.909819+00:00
-- url     : https://prove2.me/theorems/de149cf0-cc4e-4767-ac1d-28e91533a2fd
-- title:
--   Proof of Proposition 4.1 (bid shading), p. ec 38 — G^S₁(µ₁) strictly decreases for µ₁ ≥ 0 with (1+µ₁)c ≤ sup X₁
-- statement:
--   In the symmetric correlated setting, let every buyer use the same shading parameter $\mu_1\ge0$ under bid shading, and let $G_1^{S}(\mu_1)$ be one buyer's expected expenditure:
--   $$G_1^S(\mu_1)=T\,\mathbb E\Big[\Big(\max_{i\ne1}\tfrac{x_i}{1+\mu_1}\vee c\Big)\mathbf 1\Big\{\tfrac{x_1}{1+\mu_1}\ge\max_{i\ne1}\tfrac{x_i}{1+\mu_1}\vee c\Big\}\Big].$$
--   Then $G_1^S$ is strictly decreasing on $\{\mu_1\ge0:(1+\mu_1)c\le\sup X_1\}$.
--
--   Every parameter space $S_1=[0,\bar\mu]$ of Theorem 3.2 lies in this set; this is the monotonicity behind Proposition 4.1 for bid shading and the first step of Lemma B.3.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - reading: bid shading's parameter space is printed S_i = [1, µ̄_i] on p. ec 4 and S_i = [0, µ̄_i] on p. ec 5 → lower end 0; reason: Table 1 has µ_i ≥ 0 and p. ec 5 has [0, µ̄_i]; with [1, µ̄] property (ii) of p. ec 44 fails
--   - generalization: G^S₁ strictly decreases for µ₁ ∈ S₁, the parameter space determined in Theorem 3.2 → strict decrease on {µ₁ : 0 ≤ µ₁, (1+µ₁)c ≤ v̄}; reason: this set contains every S₁ = [0, µ̄] of Theorem 3.2
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. ec 38, proof of Proposition 4.1 (Bid Shading), (B-21)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Proof of Proposition 4.1 (bid shading), p. ec 38: at symmetric profiles, one buyer's expected
expenditure under bid shading, `G^S₁(μ₁)`, strictly decreases in `μ₁` over
`{μ₁ ≥ 0 : (1 + μ₁) c ≤ sup X₁}` (every parameter space `S₁ = [0, μ̄]` of Theorem 3.2 lies in this
set). -/
theorem G1_shading_strictAntiOn {n : ℕ} [NeZero n] (P : SymInstance n) :
    StrictAntiOn (G1 P .shading) {μ | 0 ≤ μ ∧ ENNReal.ofReal ((1 + μ) * P.c) ≤ P.vbar} := by sorry

end BudgetMgmt.Profit
