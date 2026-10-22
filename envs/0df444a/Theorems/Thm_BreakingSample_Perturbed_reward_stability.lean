-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_reward_stability
-- name    : BreakingSample.Perturbed.reward_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:09.354579+00:00
-- url     : https://prove2.me/theorems/03bfc49c-8b32-4052-a7ad-9e87dee03596
-- title:
--   §6.3.4, before (49) — policy value is stable under reward perturbation
-- statement:
--   Keep a transition kernel and deterministic policy fixed, with $0\le\gamma<1$. If the immediate rewards $r$ and $r'$ differ by at most $\xi$ at every state-action pair, then their policy values satisfy
--
--   $$|V_r^\pi(s)-V_{r'}^\pi(s)|\le\frac{\xi}{1-\gamma}\qquad(s\in S).$$
--
--   This bounds how much a bounded reward perturbation changes the performance of any fixed policy.
--
--   **Formalization Note** The statement allows real rewards. The paper's displayed identity just before this inequality omits a discount factor inside a resolvent; the displayed bound uses the discounted resolvent and is the claim formalized here.
-- source:
--   arXiv:2005.12900v8, §6.3.4, display before (49), p. 18

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BreakingSample.Perturbed

open FoundationsML.ReinforcementLearning

/-- The reward perturbation bound in §6.3.4 before (49), arXiv:2005.12900v8, p. 18. -/
theorem reward_stability {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (r r' : S → A → ℝ) (γ ξ : ℝ)
    (hP : IsTransitionKernel P) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hξ : 0 ≤ ξ) (hr : ∀ s a, |r s a - r' s a| ≤ ξ) :
    ∀ (π : S → A) (s : S),
      |value P r γ π s - value P r' γ π s| ≤ ξ / (1 - γ) := by sorry

end BreakingSample.Perturbed
