-- Prove2me | Theorems.Thm_BreakingSample_Conservative_lemma_3
-- name    : BreakingSample.Conservative.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:39.728312+00:00
-- url     : https://prove2.me/theorems/5377b7d9-b55a-4068-80c9-84e84dd4a277
-- title:
--   Lemma 3, p. 16 — with u⋆ = r(s,a) + γ(PV⋆)_{s,a} − γV⋆(s), Q⋆_{s,a,u⋆} = Q⋆ and V⋆_{s,a,u⋆} = V⋆
-- statement:
--   Let $\mathcal M = (\mathcal S,\mathcal A,P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma \in (0,1)$, and fix a pair $(s,a)$. Set
--
--   $$u^\star := r(s,a) + \gamma \sum_{s'} P(s'\mid s,a) V^\star(s') - \gamma V^\star(s).$$
--
--   Then the $(s,a)$-absorbing MDP $\mathcal M_{s,a,u^\star}$ of (39), with reward $u^\star$ at $(s,a)$, has the same optimal Q-function and the same optimal value function as $\mathcal M$:
--
--   $$Q^\star_{s,a,u^\star} = Q^\star \qquad\text{and}\qquad V^\star_{s,a,u^\star} = V^\star.$$
--
--   By Remark 5 the lemma does not use the form of $P$; it is applied to the empirical kernel $\widehat P$, where it replaces $\widehat{\mathcal M}$ by an absorbing MDP whose dependence on the samples for $(s,a)$ is carried by one scalar.
--
--   **Formalization Note** Stated for any transition kernel. The optimal functions of the absorbing MDP are those of the module *Model* applied to the absorbing kernel and reward.
-- source:
--   arXiv:2005.12900v8, Lemma 3, p. 16, (40); Remark 5, p. 16

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Conservative

theorem lemma_3 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ) (s : S) (a : A) :
    let uStar : ℝ := r s a + γ * ∑ s', P s a s' * BreakingSample.Perturbed.optValue P r γ s' - γ * BreakingSample.Perturbed.optValue P r γ s
    BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a uStar) γ = BreakingSample.Perturbed.optQ P r γ ∧
      BreakingSample.Perturbed.optValue (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a uStar) γ = BreakingSample.Perturbed.optValue P r γ := by sorry

end BreakingSample.Conservative
