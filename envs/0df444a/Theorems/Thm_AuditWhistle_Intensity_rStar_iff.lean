-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_rStar_iff
-- name    : AuditWhistle.Intensity.rStar_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:37.544256+00:00
-- url     : https://prove2.me/theorems/1fb8ec06-ede8-4b7f-bf4a-06c47c8c638e
-- title:
--   Appendix, proof of Proposition 2, p. 33 — lim_{a*→0} ∂V/∂τ > 0 if and only if r > r* on the branch e₁* = 1
-- statement:
--   Fix a model, write $r=R/\gamma$, $d=D/k$, and let $V_1(a)=a-(1-p)d\,[\beta\tau+(1-\beta\tau)e_0(a,\tau)]$ be the gap function on the branch $e_1=1$. For $\tau\in(0,1)$ the limit
--   $$L=\lim_{a\to0^+}\frac{\partial V_1}{\partial\tau}(a)$$
--   exists, and
--   $$L>0\iff r>r^*=\frac{\beta\,[\tau(\beta-2\beta p+p)-1]^2}{(p-1)(\beta\tau-1)\,[\beta-\beta^2\tau+(2\beta-1)p(\beta\tau+1)]}.$$
--
--   The threshold $r^*$ is the enforcer-incentive threshold of Proposition 2.
--
--   **Formalization Note** The paper's $\partial V(a^*)/\partial\tau$ here is taken on the conjectured branch $e_1^*=1$, which is why $V_1$ is used. The partial derivative is Mathlib's `deriv` of $t\mapsto V_1(t,a)$ at $\tau$; this function is a rational function with nonvanishing denominator near $\tau$, so the derivative exists. The limit is one-sided because audit quality lives in $(0,1)$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 33, Appendix, proof of Proposition 2

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
import Definitions.Def_AuditWhistle_Intensity_Reaction

namespace AuditWhistle.Intensity

theorem rStar_iff (M : Model) (τ : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1) :
    ∃ L : ℝ,
      Filter.Tendsto (fun a => deriv (fun t => V1 M t a) τ) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
      (0 < L ↔ rStar M.p M.β τ < M.R / M.γ) := by sorry

end AuditWhistle.Intensity
