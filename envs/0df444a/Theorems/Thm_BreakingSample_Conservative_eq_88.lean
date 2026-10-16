-- Prove2me | Theorems.Thm_BreakingSample_Conservative_eq_88
-- name    : BreakingSample.Conservative.eq_88
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:55.950788+00:00
-- url     : https://prove2.me/theorems/3a70be39-711a-421c-ac27-1891922fa61d
-- title:
--   (88), App. B.3, p. 29 — the optimal Q-function of the (s,a)-absorbing MDP is (1/(1−γ))-Lipschitz in u
-- statement:
--   Let $(\mathcal S,\mathcal A,\widehat P,r,\gamma)$ be a finite discounted MDP with rewards in $[0,1]$ and $\gamma\in(0,1)$, fix a pair $(s,a)$, and let $\widehat Q^\star_{s,a,u}$ be the optimal Q-function of the $(s,a)$-absorbing MDP $\widehat{\mathcal M}_{s,a,u}$ of (39). For all real $u, u'$,
--
--   $$\big\|\widehat Q^\star_{s,a,u} - \widehat Q^\star_{s,a,u'}\big\|_\infty \le \frac{1}{1-\gamma}\,|u - u'|.$$
--
--   Together with Lemma 3 this shows that a net point $u_0$ close to $\widehat u^\star$ yields an absorbing MDP whose optimal Q-function is close to $\widehat Q^\star$, which is (56).
--
--   **Formalization Note** The sup norm is written entrywise. The paper cites Agarwal et al. (2020, Lemma 8) for the proof. Stated for any kernel and any real $u, u'$ (the paper restricts $|u| \le 1/(1-\gamma)$ in the construction; the inequality does not need it).
-- source:
--   arXiv:2005.12900v8, App. B.3, p. 29, (88)

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Conservative

theorem eq_88 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ) (hM : BreakingSample.Perturbed.IsDiscountedMDP P r γ)
    (s : S) (a : A) (u u' : ℝ) :
    ∀ s' a', |BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u) γ s' a'
        - BreakingSample.Perturbed.optQ (BreakingSample.Perturbed.absorbKernel P s a) (BreakingSample.Perturbed.absorbReward r s a u') γ s' a'| ≤ 1 / (1 - γ) * |u - u'| := by sorry

end BreakingSample.Conservative
