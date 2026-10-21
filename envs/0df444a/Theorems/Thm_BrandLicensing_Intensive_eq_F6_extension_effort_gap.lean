-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_F6_extension_effort_gap
-- name    : BrandLicensing.Intensive.eq_F6_extension_effort_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:07.399394+00:00
-- url     : https://prove2.me/theorems/bf7f0527-90cb-429b-b01e-5ba72b9f280f
-- title:
--   Eqs. (F.5), (F.6), p. 3196 — at the intensive margin the extension effort is higher under licensing
-- statement:
--   Under the standing assumptions, with $\Xi$ and $D$ as above, the difference between the closed-form extension efforts (A.2) and (B.2) is
--   $$e^H_E-e^L_E=(1-\alpha)\mu\left\{\frac{\lambda[2-(1-\alpha)^2\rho]+\rho}{\Xi}-\frac{(1+\lambda)\rho}{D}\right\}.$$
--   If moreover $\rho>0$, $\alpha<1$, the denominator of (F.2) is non-zero and $\theta=\theta_I$, then
--   $$e^H_E-e^L_E=-(1-\alpha)\mu\rho\,\frac{2-\rho-\lambda\{2-[2-(2-\alpha)\alpha]\rho\}}{D\,\{\lambda[2-(1-\alpha)^2\rho]+\rho\}}<0.$$
--
--   This is the sign computation behind Proposition 3: at the intensive margin the extension is of higher quality under licensing.
--
--   **Formalization Note** Two printed slips are corrected. The right-hand side of the printed (F.5) is $e^L_E-e^H_E$, not $e^H_E-e^L_E$; the statement above has the sign reversed accordingly. The printed (F.6) has $2-\rho+\lambda\{\dots\}$ in the numerator; the correct factor is $2-\rho-\lambda\{\dots\}$, which is positive for $\rho>0$, $\alpha<1$, so the paper's conclusion (negative) stands.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3196 (PDF 16), Appendix F, eqs. (F.5), (F.6)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (F.5), (F.6), p. 3196, sign-corrected: the difference between the extension efforts, and its
value at `θ = θ_I`, which is negative. -/
theorem eq_F6_extension_effort_gap (P : Params) (hP : P.Standing) :
    eEH_cf P - eEL_cf P =
      (1 - P.α) * P.μ
        * ((P.lam * (2 - (1 - P.α) ^ 2 * P.ρ) + P.ρ) / Xi P - (1 + P.lam) * P.ρ / Dlic P) ∧
    (0 < P.ρ → P.α < 1 → thetaI_den P ≠ 0 → P.θ = thetaI P →
      eEH_cf P - eEL_cf P =
        -((1 - P.α) * P.μ * P.ρ * (2 - P.ρ - P.lam * (2 - (2 - (2 - P.α) * P.α) * P.ρ))
          / (Dlic P * (P.lam * (2 - (1 - P.α) ^ 2 * P.ρ) + P.ρ))) ∧
      eEH_cf P - eEL_cf P < 0) := by sorry
end BrandLicensing.Intensive
