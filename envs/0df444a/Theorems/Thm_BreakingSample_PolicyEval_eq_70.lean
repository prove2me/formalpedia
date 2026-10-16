-- Prove2me | Theorems.Thm_BreakingSample_PolicyEval_eq_70
-- name    : BreakingSample.PolicyEval.eq_70
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:48.866683+00:00
-- url     : https://prove2.me/theorems/d3b66440-9071-478f-bc9f-7f053dbd1355
-- title:
--   (70), p. 24 (Azar et al. 2013, Lemma 8) — ‖(I − γP_π)⁻¹√Var_{P_π}(V^π)‖∞ ≤ 2log2/(γ(1−γ)^{1.5})‖r‖∞
-- statement:
--   Let $P$ be a transition kernel on finite state and action sets, $r\ge0$ a nonnegative reward, $0<\gamma<1$, $\pi$ a deterministic policy and $V^\pi$ its value function. Then
--   $$
--   \Big\|(I-\gamma P_\pi)^{-1}\sqrt{\mathrm{Var}_{P_\pi}(V^\pi)}\Big\|_\infty\le\frac{2\log 2}{\gamma(1-\gamma)^{1.5}}\,\|r\|_\infty ,
--   $$
--   where $\|r\|_\infty=\max_{s,a}|r(s,a)|$ and $\log$ is the natural logarithm.
--
--   This is the classical "total variance" bound, which the paper attributes to Azar, Munos and Kappen (2013, Lemma 8) and uses to pass from the instance-dependent bound (80) to the worst-case rate of Lemma 2 and Lemma 1.
--
--   **Formalization Note** The paper's standing rewards lie in $[0,1]$; both sides scale linearly in $r$, so the statement for all nonnegative $r$ is equivalent. The paper quotes this bound without proof.
-- source:
--   arXiv:2005.12900v8, (70), App. B.1, p. 24 (citing Azar, Munos, Kappen 2013, Lemma 8)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_BreakingSample_Perturbed_Model

namespace BreakingSample.PolicyEval

open FoundationsML.ReinforcementLearning Matrix

/-- (70), arXiv:2005.12900v8, App. B.1, p. 24 (due to Azar et al. 2013, Lemma 8): for the value
function `V^π`, `‖(I − γP_π)⁻¹ √Var_{P_π}(V^π)‖∞ ≤ 2 log 2/(γ(1 − γ)^{1.5}) ‖r‖∞`, for any nonnegative
reward `r`; `‖r‖` is the maximum of `|r(s,a)|` over all state-action pairs. -/
theorem eq_70 {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P) (r : S → A → ℝ) (hr : ∀ s a, 0 ≤ r s a)
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (π : S → A) :
    ‖BreakingSample.Perturbed.resolvent P γ π *ᵥ (fun s => Real.sqrt (BreakingSample.Perturbed.varPi P π (BreakingSample.Perturbed.value P r γ π) s))‖ ≤
      2 * Real.log 2 / (γ * (1 - γ) ^ (1.5 : ℝ)) * ‖r‖ := by sorry

end BreakingSample.PolicyEval
