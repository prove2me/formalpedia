-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_F4_core_effort_gap
-- name    : BrandLicensing.Intensive.eq_F4_core_effort_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:19.521414+00:00
-- url     : https://prove2.me/theorems/0509d036-0143-4c15-a472-dec51c7a8730
-- title:
--   Eqs. (F.3), (F.4), p. 3196 — at the intensive margin the core effort is higher under in-house development
-- statement:
--   Under the standing assumptions, with $\Xi$ and $D$ as above, the difference between the closed-form core efforts (A.1) and (15) is
--   $$e^H_C-e^L_C=(1-\alpha)^2\mu\rho\,\frac{\lambda\rho[(\alpha-2)\alpha(\theta-1)+\theta-2]+2\theta(1-\lambda)-2\theta\rho+4\lambda+\rho}{D\,\Xi}\qquad(F.3).$$
--   If moreover $\rho>0$, $\alpha<1$, the denominator of (F.2) is non-zero and $\theta=\theta_I$, then
--   $$e^H_C-e^L_C=(1-\alpha)^2\lambda\mu\rho\,\frac{2-\rho-\lambda\{2-[2-(2-\alpha)\alpha]\rho\}}{D\,\{\lambda[2-(1-\alpha)^2\rho]+\rho\}},$$
--   which is non-negative, and positive when $\lambda>0$.
--
--   At the intensive margin, a switch from in-house development to licensing therefore decreases the quality of the core product.
--
--   **Formalization Note** The printed (F.4) has $2-\rho+\lambda\{\dots\}$ in the numerator; the correct factor, obtained from (F.3) at $\theta=\theta_I$, is $2-\rho-\lambda\{\dots\}$, which is positive for $\rho>0$, $\alpha<1$. The page calls the difference "positive for all admissible parameter values"; it vanishes at $\lambda=0$, so positivity is stated for $\lambda>0$.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3196 (PDF 16), Appendix F, eqs. (F.3), (F.4); p. 3189 (PDF 9), §6

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (F.3), (F.4), p. 3196: the difference between the core efforts, and its value at `θ = θ_I`
(corrected numerator `2 − ρ − λ{2 − [2 − (2 − α)α]ρ}`), which is non-negative, and positive when `λ > 0`. -/
theorem eq_F4_core_effort_gap (P : Params) (hP : P.Standing) :
    eCH_cf P - eCL_cf P =
      (1 - P.α) ^ 2 * P.μ * P.ρ
        * (P.lam * P.ρ * ((P.α - 2) * P.α * (P.θ - 1) + P.θ - 2) + 2 * P.θ * (1 - P.lam)
            - 2 * P.θ * P.ρ + 4 * P.lam + P.ρ)
        / (Dlic P * Xi P) ∧
    (0 < P.ρ → P.α < 1 → thetaI_den P ≠ 0 → P.θ = thetaI P →
      eCH_cf P - eCL_cf P =
        (1 - P.α) ^ 2 * P.lam * P.μ * P.ρ
          * (2 - P.ρ - P.lam * (2 - (2 - (2 - P.α) * P.α) * P.ρ))
          / (Dlic P * (P.lam * (2 - (1 - P.α) ^ 2 * P.ρ) + P.ρ)) ∧
      0 ≤ eCH_cf P - eCL_cf P ∧ (0 < P.lam → 0 < eCH_cf P - eCL_cf P)) := by sorry
end BrandLicensing.Intensive
