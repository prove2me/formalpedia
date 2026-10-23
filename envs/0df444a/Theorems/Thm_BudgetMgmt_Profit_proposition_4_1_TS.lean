-- Prove2me | Theorems.Thm_BudgetMgmt_Profit_proposition_4_1_TS
-- name    : BudgetMgmt.Profit.proposition_4_1_TS
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:25.823231+00:00
-- url     : https://prove2.me/theorems/ef24b09d-dadd-4afc-ba23-883528b3a886
-- title:
--   Proposition 4.1, p. 22 — thresholding and bid shading cases: unique symmetric system equilibrium, the solution of G₁(s₁) ≤ B₁ ⊥ s₁ ≥ s̲₁
-- statement:
--   Fix a symmetric correlated instance. For **thresholding** with parameter space $[c,\bar\tau]$ and for **bid shading** with parameter space $[0,\bar\mu]$, for every admissible upper end:
--   1. the mechanism admits exactly one symmetric system equilibrium $s_1^*\vec 1$ (Definition 2.1);
--   2. a symmetric profile $s_1\vec1$ is a system equilibrium if and only if $s_1\in\hat S_1=[\underline s_1,\bar s_1]$ solves the one-variable non-linear complementarity problem
--   $$G_1(s_1)\le B_1\quad\perp\quad s_1\ge\underline s_1,$$
--   that is, both inequalities hold and at least one holds with equality; here $\underline s_1=c$ for thresholding and $\underline s_1=0$ for bid shading.
--
--   Uniqueness is what makes the dominance relations of Theorem 4.2 well defined: they compare "the" symmetric system equilibria of two mechanisms.
--
--   **Scope.** Proposition 4.1 is stated for all six mechanisms of Table 1. This mission models the three compared in Theorem 4.2 part 1; this item states the thresholding and bid shading cases, and `proposition_4_1_R` states the reserve pricing case. The multiplicative boosting, alternative multiplicative boosting and throttling cases are not stated (no definitions of those mechanisms in this mission).
--
--   **Formalization Note** "Under the assumptions of Theorem 3.2" is carried by the instance and by the admissibility of the upper ends.
--
--   Differences from the source:
--   - reading: X_i ⊆ ℝ₊ the (possibly unbounded) support of buyer i's values, 0 ∈ X_i, c ∈ int(X_i) (p. 5) → X_i = [0, v̄) with c < v̄ ≤ ∞ for every buyer; reason: the paper's proofs treat X_i as an interval (∂H/∂y₁ < 0 'as long as τ₁ ∈ int(X₁)', S_i = [c, sup X_i]); with a gap in X_i, G₁ is constant across the gap and the uniqueness of Proposition 4.1 fails, so the statements are made for interval supports; exchangeability makes all X_i equal; open versus closed upper end is a null set
--   - reading: F has a continuous and positive density f (p. 5) → f is continuous on [0, v̄)ⁿ, positive on its interior (0, v̄)ⁿ and zero outside [0, v̄)ⁿ; reason: continuity and positivity are read on the support; positivity on the null boundary faces is not required, which only weakens the hypothesis
--   - generalization: the conditional expectations E[x_i | x_{−i} ≤ z_{−i}] and E[x_i | max_{j≠i} x_j = y] are bounded (p. 5) → not assumed; only E[x_i] < ∞ is kept; reason: the paper uses these bounds only to show that large enough upper ends of the parameter spaces exist when the support is unbounded (pp. ec 7, ec 9); here the upper ends are hypotheses, and every instance of the paper satisfies the remaining assumptions
--   - encoding: ties are broken arbitrarily (p. 10) → ties are broken in favour of the lowest index; reason: ties have probability zero under a density, so every expectation is unchanged
--   - encoding: (x₁, …, x_n) has the same law as (x_σ(1), …, x_σ(n)) for every permutation σ (p. 21) → f(x ∘ σ) = f(x) for every permutation σ and every x; reason: for a density continuous on the permutation-invariant box and zero outside it, distributional exchangeability is equivalent to pointwise invariance of f
--   - encoding: T items, n buyers, buyer 1 the reference buyer → T : ℕ with 0 < T; n : ℕ with [NeZero n]; buyer 1 is index 0 : Fin n; reason: Lean indexing; the paper's T counts items and buyer 1 exists
--   - reading: bid shading's parameter space is printed S_i = [1, µ̄_i] on p. ec 4 and S_i = [0, µ̄_i] on p. ec 5 → lower end 0; reason: Table 1 has µ_i ≥ 0 and p. ec 5 has [0, µ̄_i]; with [1, µ̄] property (ii) of p. ec 44 fails
--   - generalization: the upper ends of the parameter spaces of thresholding and bid shading are the specific values chosen in the proof of Theorem 3.2 (sup X_i or 'large enough', pp. ec 5, ec 7, ec 9) → every upper end satisfying the conditions that proof imposes (inside the support, budget met at the upper end for every profile of the others in the space; for reserve pricing also r̄ ≥ r̲_i(r_{−i})); reason: the paper's own choices satisfy these conditions, so the statement covers them
-- source:
--   Balseiro, Kim, Mahdian & Mirrokni, Budget management strategies in repeated auctions, SSRN 2858261 (version of July 8, 2020), p. 22, Proposition 4.1; proof pp. ec 37–39

import Mathlib
import Definitions.Def_BudgetMgmt_Profit_Model

namespace BudgetMgmt.Profit

/-- Proposition 4.1, p. 22, for thresholding and bid shading: for every admissible upper end, the
mechanism admits a unique symmetric system equilibrium (Definition 2.1), and a symmetric profile
`s₁ 1⃗` is a system equilibrium iff `s₁ ∈ Ŝ₁ = [s̲₁, s̄₁]` solves the one-variable complementarity
problem `G₁(s₁) ≤ B₁ ⊥ s₁ ≥ s̲₁` (both inequalities hold and at least one is tight), with
`s̲₁ = c` for thresholding and `s̲₁ = 0` for bid shading. -/
theorem proposition_4_1_TS {n : ℕ} [NeZero n] (P : SymInstance n) :
    (∀ taubar : ℝ, AdmissibleT P taubar →
      (∃! τ : ℝ, IsSymSysEq P .thresholding P.c taubar τ) ∧
      ∀ τ : ℝ, IsSymSysEq P .thresholding P.c taubar τ ↔
        (τ ∈ Set.Icc P.c taubar ∧ G1 P .thresholding τ ≤ P.B ∧
          (G1 P .thresholding τ = P.B ∨ τ = P.c))) ∧
    (∀ mubar : ℝ, AdmissibleS P mubar →
      (∃! μ : ℝ, IsSymSysEq P .shading 0 mubar μ) ∧
      ∀ μ : ℝ, IsSymSysEq P .shading 0 mubar μ ↔
        (μ ∈ Set.Icc 0 mubar ∧ G1 P .shading μ ≤ P.B ∧
          (G1 P .shading μ = P.B ∨ μ = 0))) := by sorry

end BudgetMgmt.Profit
