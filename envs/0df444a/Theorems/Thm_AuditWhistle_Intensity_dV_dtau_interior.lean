-- Prove2me | Theorems.Thm_AuditWhistle_Intensity_dV_dtau_interior
-- name    : AuditWhistle.Intensity.dV_dtau_interior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:18:21.756981+00:00
-- url     : https://prove2.me/theorems/632eb630-77f8-4d2a-baa4-38c35cbf69b2
-- title:
--   Appendix, proof of Proposition 2, p. 34 — closed form and negativity of ∂V/∂τ when e₁* < 1
-- statement:
--   Fix a model, write $r=R/\gamma$, $d=D/k$, and let $V$ be the gap function (28). Let $\tau\in(0,1)$ and $a\in(0,1)$ with
--   $$r\,\frac{(1-p)(1-a)\beta}{(1-p)(1-a)\beta+p(1-\beta)}<1,$$
--   so that $e_1(a)<1$. Then $\tau\mapsto V(a)$ is differentiable at $\tau$ with
--   $$\frac{\partial V}{\partial\tau}=\frac{(a-1)(1-2\beta)^2d(p-1)^2p^2r}{[a\beta(p-1)+\beta-2\beta p+p]\,[a(p-1)(\beta\tau-1)+\beta\tau+p(\tau-2\beta\tau)-1]^2},$$
--   and this value is negative.
--
--   It shows that on the branch $e_1^*<1$ whistleblowing intensity always raises audit quality, which is the "only if" half of Proposition 2 off the branch $e_1^*=1$.
--
--   **Formalization Note** The identity is stated for every $a\in(0,1)$ in the branch, not only at the equilibrium $a^*$; the paper applies it at $a^*$.
-- source:
--   Nan, Tang & Ye, Auditing with a Chance of Whistleblowing, author manuscript dated December 30, 2024 (Management Science, DOI 10.1287/mnsc.2024.04808), p. 34, Appendix, proof of Proposition 2

import Mathlib
import Definitions.Def_AuditWhistle_Intensity_Setting
import Definitions.Def_AuditWhistle_Intensity_Reaction

namespace AuditWhistle.Intensity

theorem dV_dtau_interior (M : Model) (τ a : ℝ) (hτ : τ ∈ Set.Ioo (0:ℝ) 1)
    (ha : a ∈ Set.Ioo (0:ℝ) 1)
    (hint : M.R / M.γ * ((1 - M.p) * (1 - a) * M.β /
      ((1 - M.p) * (1 - a) * M.β + M.p * (1 - M.β))) < 1) :
    HasDerivAt (fun t => V M t a)
      ((a - 1) * (1 - 2 * M.β) ^ 2 * (M.D / M.k) * (M.p - 1) ^ 2 * M.p ^ 2 * (M.R / M.γ) /
        ((a * M.β * (M.p - 1) + M.β - 2 * M.β * M.p + M.p) *
          (a * (M.p - 1) * (M.β * τ - 1) + M.β * τ + M.p * (τ - 2 * M.β * τ) - 1) ^ 2)) τ ∧
    (a - 1) * (1 - 2 * M.β) ^ 2 * (M.D / M.k) * (M.p - 1) ^ 2 * M.p ^ 2 * (M.R / M.γ) /
        ((a * M.β * (M.p - 1) + M.β - 2 * M.β * M.p + M.p) *
          (a * (M.p - 1) * (M.β * τ - 1) + M.β * τ + M.p * (τ - 2 * M.β * τ) - 1) ^ 2) < 0 := by sorry

end AuditWhistle.Intensity
