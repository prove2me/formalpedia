-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_lemma_10
-- name    : BreakingSample.PolicyEval.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:41.496988+00:00
-- url     : https://prove2.me/theorems/8cd223c7-4b87-45e2-acb0-a9342884a691
-- title:
--   Lemma 10 (a)–(e), p. 23 — (I − γP_π)⁻¹ = Σᵢ(γP_π)ⁱ is entrywise nonnegative, has row sums 1/(1−γ), and is monotone on nonnegative vectors
-- statement:
--   Let $P$ be a transition kernel on finite state and action sets, $\pi$ a deterministic policy, $P_\pi(s,s')=P(s'\mid s,\pi(s))$ its state transition matrix, and $0<\gamma<1$. Then:
--
--   1. the Neumann series converges to the resolvent: $$(I-\gamma P_\pi)^{-1}=\sum_{i=0}^\infty(\gamma P_\pi)^i;$$
--   2. every entry of $(I-\gamma P_\pi)^{-1}$ is nonnegative;
--   3. $\|(I-\gamma P_\pi)^{-1}\|_1\le 1/(1-\gamma)$, where $\|M\|_1=\max_i\sum_j|M_{ij}|$ is the maximum absolute row sum;
--   4. $(1-\gamma)(I-\gamma P_\pi)^{-1}\mathbf 1=\mathbf 1$, where $\mathbf 1$ is the all-ones vector;
--   5. for vectors $0\le r_1\le r_2$ (entrywise), $0\le(I-\gamma P_\pi)^{-1}r_1\le(I-\gamma P_\pi)^{-1}r_2$.
--
--   These elementary facts are used throughout the analysis: nonnegativity and monotonicity let entrywise bounds pass through the resolvent, and (3)–(4) say that $(1-\gamma)(I-\gamma P_\pi)^{-1}$ is a stochastic matrix.
--
--   **Formalization Note** The series converges in the entrywise topology on matrices (`HasSum`). Item 3 is stated row by row, which avoids choosing a matrix norm instance. The paper adds that the same facts hold for the state-action matrix $P^\pi$; that variant is not used by this mission and is not stated.
-- source:
--   arXiv:2005.12900v8, Lemma 10 (a)–(e), App. A, p. 23; ‖·‖₁ from §2.3, p. 7

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- Lemma 10 (a)–(e), arXiv:2005.12900v8, App. A, p. 23: elementary facts on the resolvent
`(I − γP_π)⁻¹` of a policy's state transition matrix. (c) is `‖(I − γP_π)⁻¹‖₁ ≤ 1/(1−γ)` with
`‖A‖₁ := max_i ∑_j |A_ij|` (p. 7). -/
theorem lemma_10 {S A : Type} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A) (γ : ℝ) (hγ₀ : 0 < γ)
    (hγ₁ : γ < 1) :
    HasSum (fun i : ℕ => (γ • BreakingSample.Perturbed.policyMatrix P π) ^ i) (BreakingSample.Perturbed.resolvent P γ π) ∧
    (∀ i j, 0 ≤ BreakingSample.Perturbed.resolvent P γ π i j) ∧
    (∀ i, ∑ j, |BreakingSample.Perturbed.resolvent P γ π i j| ≤ 1 / (1 - γ)) ∧
    (∀ s, (1 - γ) * (BreakingSample.Perturbed.resolvent P γ π *ᵥ fun _ => (1 : ℝ)) s = 1) ∧
    (∀ r₁ r₂ : S → ℝ, (∀ s, 0 ≤ r₁ s) → (∀ s, r₁ s ≤ r₂ s) →
      ∀ s, 0 ≤ (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₁) s ∧
        (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₁) s ≤ (BreakingSample.Perturbed.resolvent P γ π *ᵥ r₂) s) := by sorry

end BreakingSample.PolicyEval
