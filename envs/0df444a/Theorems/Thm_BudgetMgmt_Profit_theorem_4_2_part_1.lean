-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_theorem_4_2_part_1
-- name    : BudgetMgmt.Profit.theorem_4_2_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:27.772346+00:00
-- url     : https://prove2.me/theorems/7a19b197-1f82-4742-88a0-96487c1f406b
-- title:
--   Theorem 4.2 part 1, p. 25 — at symmetric system equilibria, reserve pricing (under Assumption 1) earns at least thresholding's profit, and thresholding at least bid shading's
-- statement:
--   Consider a symmetric correlated instance: $n$ buyers with a common budget $B_1$, an exchangeable joint value density, $T$ items at opportunity cost $c$. Compare the seller's profit
--   $$P(s)=\sum_{i=1}^nG_i(s)-c\,I(s)$$
--   at the symmetric system equilibria of three budget management mechanisms of Table 1: reserve pricing (R), thresholding (T) and bid shading (S). Theorem 4.2, part 1, states, for the profit objective,
--   $$\text{Reserve Pricing}\ \ge_{SIF}\ \text{Thresholding}\ \ge\ \text{Bid Shading}.$$
--   Precisely, for every admissible choice of the upper ends $\bar\tau$, $\bar\mu$, $\bar r$ of the parameter spaces $[c,\bar\tau]$, $[0,\bar\mu]$ and reserve pricing's restricted space:
--   1. if $\tau_1\vec 1$ is a symmetric system equilibrium of thresholding and $\mu_1\vec1$ one of bid shading (Definition 2.1), then $P^S(\mu_1)\le P^T(\tau_1)$;
--   2. if moreover the value distribution satisfies Assumption 1, and $r_1\vec1$ is a symmetric restricted system equilibrium of reserve pricing (Definition A.1), then $P^T(\tau_1)\le P^R(r_1)$.
--
--   "$\pi\ge\pi'$" means that the symmetric system equilibrium of $\pi$ yields at least the profit of that of $\pi'$ for every symmetric instance (p. 22); "$\ge_{SIF}$" restricts to distributions satisfying Assumption 1. Proposition 4.1 guarantees that these equilibria exist and are unique, so quantifying over all of them is the paper's comparison.
--
--   The result says that, when a platform manages budgets on behalf of advertisers, pacing through reserve prices is at least as profitable for the seller as thresholding, which in turn beats bid shading.
--
--   **Formalization Note** The profit is the page's $\sum_iG_i-cI$, not the derived $nG_1-cI$. The upper ends of the parameter spaces are not fixed: the statement holds for every choice satisfying the conditions of the proof of Theorem 3.2.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - reading: bid shading's parameter space is printed S_i = [1, µ̄_i] on p. ec 4 and S_i = [0, µ̄_i] on p. ec 5 → lower end 0; reason: Table 1 has µ_i ≥ 0 and p. ec 5 has [0, µ̄_i]; with [1, µ̄] property (ii) of p. ec 44 fails
--   - encoding: ξ_i(z_i, z_{−i}) = z_i f_i(z_i | x_{−i} ≤ z_{−i}) / F̄_i(z_i | x_{−i} ≤ z_{−i}) (p. ec 8) → z_i · ∂_t ℙ(x_i ≤ t, x_{−i} ≤ z_{−i})|_{t=z_i} / ℙ(x_i ≥ z_i, x_{−i} ≤ z_{−i}); reason: the factor ℙ(x_{−i} ≤ z_{−i}) cancels and ℙ(x_i = z_i) = 0; the ratio is evaluated only where every coordinate is positive and below v̄, where the denominator is positive
--   - reading: Assumption 1 (p. ec 9): ξ_i jointly continuous in z; ξ_i(z_i, z_i ∨ z_{−i}) strictly increasing in z_i for z_{−i} ∈ X_{−i} → continuity on the open box (0, v̄)ⁿ and strict increase for z_i ∈ (0, v̄); reason: ξ_i is undefined (0/0) where some z_j, j ≠ i, is 0; the reading on the interior is the weaker hypothesis, and at z_i = 0 the value ξ_i = 0 adds nothing
--   - encoding: S' = {r : r_i ∈ [r̲_i, r̄_i], r_i ≥ r̲_i(r_{−i})} with r̲_i(r_{−i}) the solution of ξ_i(r_i, r_i ∨ r_{−i}) = 1 and r̲_i = min r̲_i(·) ∨ c (p. ec 9) → r_i ∈ [c, r̄] and ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 whenever r_i < v̄; reason: by the page's 'ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 if r_i ≥ r̲_i(r_{−i}), and < 1 if r_i < r̲_i(r_{−i})' the two coincide under Assumption 1, and r_i ≥ r̲_i(r_{−i}) ∨ c already implies r_i ≥ r̲_i; at r_i = v̄ (bounded support) ξ's denominator vanishes and the page's constraint holds since r̲_i(r_{−i}) is interior (Claim A.4)
--   - generalization: the upper ends of the parameter spaces of thresholding, bid shading and reserve pricing are the specific values chosen in the proof of Theorem 3.2 (sup X_i or 'large enough', pp. ec 5, ec 7, ec 9) → every upper end satisfying the conditions that proof imposes (inside the support, budget met at the upper end for every profile of the others in the space; for reserve pricing also r̄ ≥ r̲_i(r_{−i})); reason: the paper's own choices satisfy these conditions, so the statement covers them
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. 25, Theorem 4.2, part 1; dominance and ≥_SIF defined p. 22; proof pp. ec 44–47 (App. B.2, B.2.1)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Theorem 4.2, part 1, p. 25: in the symmetric (correlated) setting, for the seller's profit,
Reserve Pricing ≥_SIF Thresholding ≥ Bid Shading. For every admissible choice of the parameter
spaces' upper ends: (1) the profit at a symmetric system equilibrium of thresholding is at least that
at a symmetric system equilibrium of bid shading; (2) if the value distribution satisfies
Assumption 1, the profit at a symmetric (restricted) system equilibrium of reserve pricing is at least
that at a symmetric system equilibrium of thresholding. -/
theorem theorem_4_2_part_1 {n : ℕ} [NeZero n] (P : SymInstance n) (taubar mubar : ℝ)
    (hT : AdmissibleT P taubar) (hS : AdmissibleS P mubar) :
    (∀ τ μ : ℝ, IsSymSysEq P .thresholding P.c taubar τ → IsSymSysEq P .shading 0 mubar μ →
      profit P .shading (sym μ) ≤ profit P .thresholding (sym τ)) ∧
    (Assumption1 P → ∀ rbar : ℝ, AdmissibleR P rbar → ∀ r τ : ℝ,
      IsSymRestrictedSysEq P rbar r → IsSymSysEq P .thresholding P.c taubar τ →
      profit P .thresholding (sym τ) ≤ profit P .reserve (sym r)) := by sorry

end BudgetMgmt.Profit
