-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_lemma_11
-- name    : BreakingSample.PolicyEval.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:42.114257+00:00
-- url     : https://prove2.me/theorems/c78b4b36-135f-4323-9d12-7ff698a443fa
-- title:
--   Lemma 11, p. 24 — ‖(I − γP_π)⁻¹√Var_{P_π}(V)‖∞ ≤ 4/(γ√(1−γ))‖V‖∞ for V = (I − γP_π)⁻¹r_π, r_π ≥ 0
-- statement:
--   Let $P$ be a transition kernel on finite state and action sets, $\pi$ a deterministic policy, $0<\gamma<1$, and let $r_\pi\in\mathbb R^{\mathcal S}$ be any entrywise nonnegative vector. Put $V=(I-\gamma P_\pi)^{-1}r_\pi$. Then
--   $$
--   \Big\|(I-\gamma P_\pi)^{-1}\sqrt{\mathrm{Var}_{P_\pi}(V)}\Big\|_\infty\le\frac{4}{\gamma\sqrt{1-\gamma}}\,\|V\|_\infty ,
--   $$
--   where $\mathrm{Var}_{P_\pi}(V)(s)=\sum_{s'}P_\pi(s,s')V(s')^2-\big(\sum_{s'}P_\pi(s,s')V(s')\big)^2$ and the square root is entrywise.
--
--   This bounds the total discounted standard deviation of $V$ along the chain in terms of $\|V\|_\infty$ rather than the reward; applied repeatedly it controls the auxiliary vectors $V^{(l)}$ of (36).
--
--   **Formalization Note** The vector $r_\pi$ is an arbitrary nonnegative vector, not necessarily the reward of $\pi$, exactly as on the page.
-- source:
--   arXiv:2005.12900v8, Lemma 11, (71), App. B.1, p. 24

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- Lemma 11 and (71), arXiv:2005.12900v8, App. B.1, p. 24: for `V = (I − γP_π)⁻¹ r_π` with a
nonnegative vector `r_π` (here `ρ`), `‖(I − γP_π)⁻¹ √Var_{P_π}(V)‖∞ ≤ 4/(γ√(1−γ)) ‖V‖∞`. -/
theorem lemma_11 {S A : Type} [Fintype S] [DecidableEq S]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (π : S → A) (ρ : S → ℝ)
    (hρ : ∀ s, 0 ≤ ρ s) (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) :
    ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ
        (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.resolvent P γ π *ᵥ ρ) s))‖ ≤
      4 / (γ * Real.sqrt (1 - γ)) * ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ ρ‖ := by sorry

end BreakingSample.PolicyEval
