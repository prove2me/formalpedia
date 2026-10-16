-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_eq_27
-- name    : BreakingSample.PolicyEval.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:49.784981+00:00
-- url     : https://prove2.me/theorems/484ca602-4ecf-4048-bf31-65e70a52460a
-- title:
--   (27), p. 12 — V^π = r_π + γP_πV^π and V^π = (I − γP_π)⁻¹r_π
-- statement:
--   Let $P$ be a transition kernel on finite state and action sets, $r$ any real reward, $0\le\gamma<1$ and $\pi$ a deterministic policy, with value function $V^\pi$ (the expected discounted sum of rewards (1)). Then $V^\pi$ satisfies the Bellman consistency equation and the closed form
--   $$
--   V^\pi=r_\pi+\gamma P_\pi V^\pi\qquad\text{and}\qquad V^\pi=(I-\gamma P_\pi)^{-1}r_\pi ,
--   $$
--   where $P_\pi(s,s')=P(s'\mid s,\pi(s))$ and $r_\pi(s)=r(s,\pi(s))$.
--
--   This identity connects the probabilistic definition of the value function with the matrix form in which the paper's analysis is written; in particular it identifies the plug-in estimate $\widehat V^\pi$ with $(I-\gamma\widehat P_\pi)^{-1}r_\pi$ (30).
--
--   **Formalization Note** The page states (27) for $0<\gamma<1$ and rewards in $[0,1]$; the statement here allows $\gamma=0$ and any real reward, which is a generalization.
-- source:
--   arXiv:2005.12900v8, (27), §6.1, p. 12

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- (27), arXiv:2005.12900v8, §6.1, p. 12: the value function of a deterministic policy obeys the
Bellman consistency equation `V^π = r_π + γP_πV^π` and equals `(I − γP_π)⁻¹ r_π`. -/
theorem eq_27 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (γ : ℝ) (hγ₀ : 0 ≤ γ)
    (hγ₁ : γ < 1) (π : S → A) :
    (∀ s, BreakingSample.Perturbed.value P r γ π s =
      BreakingSample.Perturbed.policyReward r π s + γ * (BreakingSample.Perturbed.policyMatrix P π *ᵥ BreakingSample.Perturbed.value P r γ π) s) ∧
    BreakingSample.Perturbed.value P r γ π = BreakingSample.Perturbed.resolvent P γ π *ᵥ BreakingSample.Perturbed.policyReward r π := by sorry

end BreakingSample.PolicyEval
