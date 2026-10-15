-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_eq_88
-- name    : BreakingSample.Perturbed.eq_88
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:02.351475+00:00
-- url     : https://prove2.me/theorems/19c660fa-84a7-4955-aa63-07edef42312c
-- title:
--   (88) — optimal absorbing Q values are Lipschitz in the reward parameter
-- statement:
--   Keep the transition kernel and every reward except that at $(s,a)$ fixed. For two rewards $u,u'$ in the paper's absorbing-MDP domain $[-1/(1-\gamma),1/(1-\gamma)]$, the optimal action-value functions obey
--
--   $$\|Q^\star_{s,a,u}-Q^\star_{s,a,u'}\|_\infty\le\frac{|u-u'|}{1-\gamma}.$$
--
--   This controls the change in optimal action values when the absorbing reward is rounded to a finite grid.
--
--   **Formalization Note** The other rewards may be arbitrary real numbers; $u$ and $u'$ remain in the interval fixed by the construction on p. 15. The kernel and $0\le\gamma<1$ are assumed.
-- source:
--   arXiv:2005.12900v8, (88), Appendix B.3, p. 29

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BreakingSample.Perturbed

open FoundationsML.ReinforcementLearning

/-- Display (88), arXiv:2005.12900v8, p. 29. -/
theorem eq_88 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hP : IsTransitionKernel P) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (s : S) (a : A) (u u' : ℝ)
    (hu : |u| ≤ 1 / (1 - γ)) (hu' : |u'| ≤ 1 / (1 - γ)) :
    ‖(fun s' a' => optQ (absorbKernel P s a) (absorbReward r s a u) γ s' a' -
      optQ (absorbKernel P s a) (absorbReward r s a u') γ s' a')‖ ≤
      (1 / (1 - γ)) * |u - u'| := by sorry

end BreakingSample.Perturbed
