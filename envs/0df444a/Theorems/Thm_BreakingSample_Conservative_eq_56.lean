-- Prove2me | Theorems.Thm_BreakingSample_Conservative_eq_56
-- name    : BreakingSample.Conservative.eq_56
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:54.989525+00:00
-- url     : https://prove2.me/theorems/95aeef7b-0721-4812-ae09-d8305afb768b
-- title:
--   (56), §6.4, p. 19 — for each (s,a) some u₀ ∈ 𝒩_{(1−γ)ω} gives ‖Q̂⋆_{s,a,u₀} − Q̂⋆‖∞ ≤ ω
-- statement:
--   Let $(\mathcal S,\mathcal A,\widehat P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in(0,1)$, with optimal Q-function $\widehat Q^\star$, and let $\omega > 0$. For every pair $(s,a)$ there is a point $u_0$ of the net $\mathcal N_{(1-\gamma)\omega}$ of (42) such that the optimal Q-function $\widehat Q^\star_{s,a,u_0}$ of the absorbing MDP $\widehat{\mathcal M}_{s,a,u_0}$ obeys
--
--   $$\big\|\widehat Q^\star_{s,a,u_0} - \widehat Q^\star\big\|_\infty \le \omega.$$
--
--   This is the first step of the decoupling argument of §6.4: the absorbing MDPs indexed by the finite net approximate the empirical MDP to accuracy $\omega$.
--
--   **Formalization Note** The sup norm is written entrywise. The rewards in $[0,1]$ are needed: they place $\widehat u^\star$ of Lemma 3 inside the range of the net. Stated for any kernel (in the paper, $\widehat P$ is the empirical kernel).
-- source:
--   arXiv:2005.12900v8, §6.4, first bullet, p. 19, (56); App. B.3, p. 29, (89)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Conservative

theorem eq_56 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (ω : ℝ) (hω : 0 < ω) :
    ∀ s a, ∃ u₀ ∈ BreakingSample.Perturbed.epsNet γ ((1 - γ) * ω), ∀ s' a',
      |BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ s' a' - BreakingSample.Perturbed.optQ P r γ s' a'| ≤ ω := by sorry

end BreakingSample.Conservative
