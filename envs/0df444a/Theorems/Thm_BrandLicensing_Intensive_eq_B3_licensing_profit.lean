-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_B3_licensing_profit
-- name    : BrandLicensing.Intensive.eq_B3_licensing_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:05.53261+00:00
-- url     : https://prove2.me/theorems/c4fe8b69-1870-4635-84c6-fa623e1b5195
-- title:
--   Eq. (B.3), p. 3195 — the brand owner's equilibrium profit under licensing
-- statement:
--   Under the standing assumptions, in every subgame-perfect equilibrium of the licensing game the brand owner's profit on the equilibrium path is
--   $$\pi^L_B=\frac{\mu\{\mu[4+(1-\alpha)^2\lambda(2+\lambda)\rho-2\rho]-2(1-\alpha)\lambda\varepsilon\{4-[3-(2-\alpha)\alpha]\rho\}\}}{2\{4-[3-(2-\alpha)\alpha]\rho\}}.$$
--
--   This is the other side of the indifference condition $\pi^H_B=\pi^L_B$ that defines the intensive margin. The equilibrium profit is unique even where the equilibrium royalty is not ($\rho=0$ or $\alpha=1$).
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3195 (PDF 15), Appendix B, eq. (B.3)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (B.3), p. 3195: the brand owner's equilibrium profit under licensing. -/
theorem eq_B3_licensing_profit (P : Params) (hP : P.Standing) (σ : LicProfile)
    (hσ : IsLicensingSPE P σ) :
    piOwnerLic P σ.eC σ.sL σ.eEL = piL_cf P := by sorry
end BrandLicensing.Intensive
