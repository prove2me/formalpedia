-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_a1_threshold
-- name    : AuditWhistle.Intensity.a1_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:28.442975+00:00
-- url     : https://prove2.me/theorems/c6e24f76-b7e3-4a65-8091-d41b1f669717
-- title:
--   Appendix, proof of Proposition 2, p. 33 — ∂²V/∂τ∂a* < 0, and for r > r* a threshold a₁ that does not depend on d
-- statement:
--   Let $V_1$ be the gap function on the branch $e_1=1$ (with $r=R/\gamma$, $d=D/k$). Then:
--
--   1. for every model and $\tau\in(0,1)$, the map $a\mapsto\partial V_1/\partial\tau(a)$ is strictly decreasing on $[0,1)$ (the paper's $\partial^2V/\partial\tau\partial a^*<0$);
--   2. for all $p,\beta,r$ and $\tau\in(0,1)$ with $r>r^*(p,\beta,\tau)$ there is a threshold $a_1>0$ such that, for **every** model with these $p$, $\beta$ and $R/\gamma=r$, whatever its $D$ and $k$, and every $a\in(0,1)$,
--   $$\frac{\partial V_1}{\partial\tau}(a)>0\iff a<a_1.$$
--
--   Part 2 is "the threshold $a_1$ does not depend on $d$": $a_1$ is chosen before the model, so it cannot depend on $D$ or $k$.
--
--   **Formalization Note** The order of quantifiers ($a_1$ before the model) encodes the independence from $d$; choosing $a_1$ after the model would lose it. The partial derivative is Mathlib's `deriv` of a function that is differentiable at $\tau$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 33, Appendix, proof of Proposition 2

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
import Definitions.Def_AuditWhistle_Intensity_Reaction

namespace AuditWhistle.Intensity

theorem a1_threshold :
    (∀ (M : Model) (τ : ℝ), τ ∈ Set.Ioo (0:ℝ) 1 →
      StrictAntiOn (fun a => deriv (fun t => V1 M t a) τ) (Set.Ico (0:ℝ) 1)) ∧
    (∀ p β r τ : ℝ, τ ∈ Set.Ioo (0:ℝ) 1 → rStar p β τ < r →
      ∃ a1 : ℝ, 0 < a1 ∧ ∀ M : Model, M.p = p → M.β = β → M.R / M.γ = r →
        ∀ a ∈ Set.Ioo (0:ℝ) 1, (0 < deriv (fun t => V1 M t a) τ ↔ a < a1)) := by sorry

end AuditWhistle.Intensity
