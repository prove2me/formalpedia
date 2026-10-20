-- Prove2me | Theorems.Thm_BreakingSample_Conservative_eq_57
-- name    : BreakingSample.Conservative.eq_57
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:02:44.025451+00:00
-- url     : https://prove2.me/theorems/e43f24d4-ab4c-4fcf-8410-8ad750e2dbce
-- title:
--   (57), §6.4, p. 19 — w.p. ≥ 1 − δ over ς, π̂c equals the conservative policy of every absorbing MDP M̂_{s,a,u₀} within ω = ξδ/(8|S||A|)
-- statement:
--   Let $(\mathcal S,\mathcal A,\widehat P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$, $\gamma\in(0,1)$ and a linearly ordered action set, and let $\xi > 0$, $\delta > 0$ and $\omega = \xi\delta/(8|\mathcal S||\mathcal A|)$. Draw $\varsigma\sim\mathrm{Unif}(0,\xi)$. With probability at least $1 - \delta$ the following holds for every pair $(s,a)$ and every net point $u_0 \in \mathcal N_{(1-\gamma)\omega}$ with $\|\widehat Q^\star_{s,a,u_0} - \widehat Q^\star\|_\infty \le \omega$: the conservative policy of the empirical MDP,
--
--   $$\widehat\pi_{\mathrm c}(s') = \min\{a' : \widehat Q^\star(s',a') > \widehat V^\star(s') - \varsigma\},$$
--
--   and the conservative policy of the absorbing MDP $\widehat{\mathcal M}_{s,a,u_0}$,
--
--   $$\widehat\pi_{s,a,u_0,\mathrm c}(s') = \min\{a' : \widehat Q^\star_{s,a,u_0}(s',a') > \widehat V^\star_{s,a,u_0}(s') - \varsigma\},$$
--
--   coincide: $\widehat\pi_{\mathrm c} = \widehat\pi_{s,a,u_0,\mathrm c}$.
--
--   By (56) such a net point exists for each $(s,a)$, so $\widehat\pi_{\mathrm c}$ is represented by a policy that does not depend on the samples of $(s,a)$; this parallels Lemma 4 for the perturbed planner.
--
--   **Formalization Note** Stronger than the page: the identity holds simultaneously for all pairs and all qualifying net points, on one event of $\varsigma$. The two policies are any policies satisfying the respective rules. Stated for any kernel (in the paper, $\widehat P$ is the empirical kernel).
-- source:
--   arXiv:2005.12900v8, §6.4, second bullet, p. 19, (57)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Sampling
import Definitions.Def_BreakingSample_Perturbed_Absorbing
import Definitions.Def_BreakingSample_Conservative_Rule

namespace BreakingSample.Conservative

theorem eq_57 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [LinearOrder A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (ξ δ : ℝ) (hξ : 0 < ξ) (hδ : 0 < δ) :
    let ω : ℝ := ξ * δ / (8 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ))
    BreakingSample.Perturbed.unifInterval ξ {ς : ℝ | ¬ ∀ (s : S) (a : A) (u₀ : ℝ), u₀ ∈ BreakingSample.Perturbed.epsNet γ ((1 - γ) * ω) →
        (∀ s' a', |BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ s' a' - BreakingSample.Perturbed.optQ P r γ s' a'| ≤ ω) →
        ∀ π π' : S → A, IsConservative (BreakingSample.Perturbed.optQ P r γ) (BreakingSample.Perturbed.optValue P r γ) ς π →
          IsConservative (BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ)
            (BreakingSample.Perturbed.optValue (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u₀) γ) ς π' → π = π'}
      ≤ ENNReal.ofReal δ := by sorry

end BreakingSample.Conservative
