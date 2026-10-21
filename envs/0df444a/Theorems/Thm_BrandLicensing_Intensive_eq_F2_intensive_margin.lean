-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_F2_intensive_margin
-- name    : BrandLicensing.Intensive.eq_F2_intensive_margin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:05.849991+00:00
-- url     : https://prove2.me/theorems/5ce47467-3c5e-4978-87ce-6a176d0557c9
-- title:
--   Eqs. (F.1), (F.2), p. 3196 — the intensive margin π^H_B = π^L_B holds exactly at θ = θ_I
-- statement:
--   Under the standing assumptions, let $\Xi=\theta[2-(1-\alpha)^2\rho]-\rho$, $D=4-[3-(2-\alpha)\alpha]\rho$, and let
--   $$\mathrm{num}=2\lambda\rho\{[5-3(2-\alpha)\alpha]\lambda-4\}-8\lambda^2-\rho^2\{[2-(2-\alpha)\alpha]\lambda-1\}^2,\qquad \mathrm{den}=\rho\{\lambda(\lambda+2)[(1-\alpha)^2\rho-2]-2\rho+2\}$$
--   be the numerator and denominator of $\theta_I=\mathrm{num}/\mathrm{den}$ in (F.2). Then, writing $\pi^H_B$ for (A.3) and $\pi^L_B$ for (B.3),
--   $$\pi^H_B-\pi^L_B=\frac{\mu^2(1-\alpha)^2(\theta\cdot\mathrm{den}-\mathrm{num})}{2\,\Xi\,D}.$$
--   Consequently, if $\rho>0$ and $\alpha<1$, then $\pi^H_B=\pi^L_B$ (F.1) holds if and only if $\mathrm{den}\ne0$ and $\theta=\theta_I$.
--
--   The intensive margin, where the brand owner is indifferent between the two modes, is thus a single value of $\theta$ for given $(\alpha,\rho,\lambda)$.
--
--   **Formalization Note** The paper solves (F.1) for $\theta$ without discussing $\mathrm{den}=0$; the statement makes that case explicit (there the margin does not exist). The hypotheses $\rho>0$, $\alpha<1$ are added: at $\alpha=1$ both profits equal $\mu^2/2$ for every $\theta$.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3196 (PDF 16), Appendix F, eqs. (F.1), (F.2)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (F.1), (F.2), p. 3196: `(A.3) − (B.3) = μ²(1 − α)²(θ·den − num)/(2ΞD)`; hence, for `ρ > 0` and
`α < 1`, the two equilibrium profits coincide exactly when `θ = θ_I = num/den` (and `den ≠ 0`). -/
theorem eq_F2_intensive_margin (P : Params) (hP : P.Standing) :
    piH_cf P - piL_cf P =
      P.μ ^ 2 * (1 - P.α) ^ 2 * (P.θ * thetaI_den P - thetaI_num P) / (2 * Xi P * Dlic P) ∧
    (0 < P.ρ → P.α < 1 →
      (piH_cf P = piL_cf P ↔ thetaI_den P ≠ 0 ∧ P.θ = thetaI P)) := by sorry
end BrandLicensing.Intensive
