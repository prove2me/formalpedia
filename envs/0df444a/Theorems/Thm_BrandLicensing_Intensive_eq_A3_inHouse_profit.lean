-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_A3_inHouse_profit
-- name    : BrandLicensing.Intensive.eq_A3_inHouse_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:09.197012+00:00
-- url     : https://prove2.me/theorems/9b1c66a2-865c-4829-a30d-b834be0fb9ad
-- title:
--   Eq. (A.3), p. 3195 — the brand owner's equilibrium profit under in-house development
-- statement:
--   Under the standing assumptions, if $(e_C,e_E)$ maximizes the in-house profit (7) over $e_C,e_E\ge0$, then the brand owner's profit there is
--   $$\pi^H_B=\frac{\mu^2\{2\theta+2(1-\alpha)^2\lambda^2-\rho[1-(1-\alpha)^2\lambda]^2\}}{2\{\theta[2-(1-\alpha)^2\rho]-\rho\}}-(1-\alpha)\varepsilon\lambda\mu.$$
--
--   This is one side of the indifference condition $\pi^H_B=\pi^L_B$ that defines the intensive margin.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3195 (PDF 15), Appendix A, eq. (A.3)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (A.3), p. 3195: the brand owner's equilibrium profit under in-house development. -/
theorem eq_A3_inHouse_profit (P : Params) (hP : P.Standing) (eC eE : ℝ)
    (h : IsInHouseEq P eC eE) :
    piInHouse P eC eE = piH_cf P := by sorry
end BrandLicensing.Intensive
