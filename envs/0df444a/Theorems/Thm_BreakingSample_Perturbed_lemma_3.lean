-- Prove2me | Theorems.Thm_BreakingSample_Perturbed_lemma_3
-- name    : BreakingSample.Perturbed.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:08.333485+00:00
-- url     : https://prove2.me/theorems/0751a267-3534-488a-b71d-495a7d6201af
-- title:
--   Lemma 3 — optimal values of a calibrated absorbing MDP
-- statement:
--   For a state-action pair $(s,a)$, set $u^\star=r(s,a)+\gamma(PV^\star)_{s,a}-\gamma V^\star(s)$ in the state-action absorbing MDP of (39). Its optimal value and optimal action value coincide with those of the original MDP:
--
--   $$V^\star_{s,a,u^\star}=V^\star,\qquad Q^\star_{s,a,u^\star}=Q^\star.$$
--
--   This calibration identifies the absorbing model whose optimal values match the original model.
-- source:
--   arXiv:2005.12900v8, Lemma 3, (40), p. 16

import Mathlib
import Definitions.Def_BreakingSample_Perturbed_Model
import Definitions.Def_BreakingSample_Perturbed_Absorbing

namespace BreakingSample.Perturbed

/-- Lemma 3 and (40), arXiv:2005.12900v8, p. 16. -/
theorem lemma_3 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    [Nonempty A] (P : S → A → S → ℝ) (r : S → A → ℝ) (γ : ℝ)
    (hM : IsDiscountedMDP P r γ) (s : S) (a : A) :
    let ustar := r s a + γ * (∑ s', P s a s' * optValue P r γ s') - γ * optValue P r γ s
    optQ (absorbKernel P s a) (absorbReward r s a ustar) γ = optQ P r γ ∧
    optValue (absorbKernel P s a) (absorbReward r s a ustar) γ = optValue P r γ := by sorry

end BreakingSample.Perturbed
