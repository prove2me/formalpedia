-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_proposition_4_1_R
-- name    : BudgetMgmt.Profit.proposition_4_1_R
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:23.933311+00:00
-- url     : https://prove2.me/theorems/1dfdf5ee-bac1-4983-af68-2633a25da183
-- title:
--   Proposition 4.1, p. 22 — reserve pricing case (correlated setting, proof pp. ec 41–42): unique symmetric restricted equilibrium, the solution of G₁(r₁) ≤ B₁ ⊥ r₁ ≥ ŝ₁
-- statement:
--   Fix a symmetric correlated instance whose distribution satisfies Assumption 1, and an admissible upper end $\bar r$ for reserve pricing. Let $\hat S_1=\{r_1: r_1\vec1\in S'\}$ be reserve pricing's symmetric parameter space and $\hat{\underline s}_1=\inf\hat S_1$ its lower end. Then:
--   1. reserve pricing admits exactly one symmetric (restricted) system equilibrium $r_1^*\vec1$ (Definition A.1);
--   2. a symmetric profile $r_1\vec1$ is one if and only if $r_1\in\hat S_1$ solves
--   $$G_1(r_1)\le B_1\quad\perp\quad r_1\ge\hat{\underline s}_1 ,$$
--   both inequalities holding and at least one with equality.
--
--   This is the reserve pricing case of Proposition 4.1, proved on pp. ec 41–42 with $\hat S_1=[\underline r_1(c\vec1_{-1})\vee c,\bar r_1]$; it is the equilibrium characterization the comparison "Reserve Pricing $\ge_{SIF}$ Thresholding" relies on.
--
--   **Scope.** See `proposition_4_1_TS`: Proposition 4.1 covers all six mechanisms of Table 1, this item its reserve pricing case.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - encoding: ξ_i(z_i, z_{−i}) = z_i f_i(z_i | x_{−i} ≤ z_{−i}) / F̄_i(z_i | x_{−i} ≤ z_{−i}) (p. ec 8) → z_i · ∂_t ℙ(x_i ≤ t, x_{−i} ≤ z_{−i})|_{t=z_i} / ℙ(x_i ≥ z_i, x_{−i} ≤ z_{−i}); reason: the factor ℙ(x_{−i} ≤ z_{−i}) cancels and ℙ(x_i = z_i) = 0; the ratio is evaluated only where every coordinate is positive and below v̄, where the denominator is positive
--   - reading: Assumption 1 (p. ec 9): ξ_i jointly continuous in z; ξ_i(z_i, z_i ∨ z_{−i}) strictly increasing in z_i for z_{−i} ∈ X_{−i} → continuity on the open box (0, v̄)ⁿ and strict increase for z_i ∈ (0, v̄); reason: ξ_i is undefined (0/0) where some z_j, j ≠ i, is 0; the reading on the interior is the weaker hypothesis, and at z_i = 0 the value ξ_i = 0 adds nothing
--   - encoding: S' = {r : r_i ∈ [r̲_i, r̄_i], r_i ≥ r̲_i(r_{−i})} with r̲_i(r_{−i}) the solution of ξ_i(r_i, r_i ∨ r_{−i}) = 1 and r̲_i = min r̲_i(·) ∨ c (p. ec 9) → r_i ∈ [c, r̄] and ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 whenever r_i < v̄; reason: by the page's 'ξ_i(r_i, r_i ∨ r_{−i}) ≥ 1 if r_i ≥ r̲_i(r_{−i}), and < 1 if r_i < r̲_i(r_{−i})' the two coincide under Assumption 1, and r_i ≥ r̲_i(r_{−i}) ∨ c already implies r_i ≥ r̲_i; at r_i = v̄ (bounded support) ξ's denominator vanishes and the page's constraint holds since r̲_i(r_{−i}) is interior (Claim A.4)
--   - generalization: the upper ends of the parameter spaces of reserve pricing are the specific values chosen in the proof of Theorem 3.2 (sup X_i or 'large enough', pp. ec 5, ec 7, ec 9) → every upper end satisfying the conditions that proof imposes (inside the support, budget met at the upper end for every profile of the others in the space; for reserve pricing also r̄ ≥ r̲_i(r_{−i})); reason: the paper's own choices satisfy these conditions, so the statement covers them
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. 22, Proposition 4.1; proof pp. ec 41–42 (Reserve Pricing in the Correlated Setting)

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Proposition 4.1, p. 22, for reserve pricing in the correlated setting (proof, pp. ec 41–42):
under Assumption 1 and for every admissible upper end `r̄`, reserve pricing admits a unique symmetric
(restricted) system equilibrium (Definition A.1), and a symmetric profile `r₁ 1⃗` is one iff
`r₁ ∈ Ŝ₁` solves `G₁(r₁) ≤ B₁ ⊥ r₁ ≥ ŝ₁` with `ŝ₁ = inf Ŝ₁`. -/
theorem proposition_4_1_R {n : ℕ} [NeZero n] (P : SymInstance n) (hA : Assumption1 P)
    (rbar : ℝ) (hR : AdmissibleR P rbar) :
    (∃! r : ℝ, IsSymRestrictedSysEq P rbar r) ∧
    ∀ r : ℝ, IsSymRestrictedSysEq P rbar r ↔
      (r ∈ ShatR P rbar ∧ G1 P .reserve r ≤ P.B ∧
        (G1 P .reserve r = P.B ∨ r = sInf (ShatR P rbar))) := by sorry

end BudgetMgmt.Profit
