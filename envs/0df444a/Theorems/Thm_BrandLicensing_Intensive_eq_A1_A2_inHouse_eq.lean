-- Prove2me | Theorems.Thm_BrandLicensing_Intensive_eq_A1_A2_inHouse_eq
-- name    : BrandLicensing.Intensive.eq_A1_A2_inHouse_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:03.341366+00:00
-- url     : https://prove2.me/theorems/f049cf3a-bd6d-45ad-bd32-b775e02e2871
-- title:
--   Eqs. (8), (9), (A.1), (A.2), pp. 3187, 3195 — the in-house equilibrium efforts
-- statement:
--   Under the standing assumptions $0\le\alpha\le1$, $\theta\ge1$, $\mu>0$, $0\le\rho<1$, $0\le\lambda\le1$, $\varepsilon>0$, let $\Xi=\theta[2-(1-\alpha)^2\rho]-\rho$. A pair $(e_C,e_E)$ maximizes the brand owner's in-house profit (7) over $e_C,e_E\ge0$ if and only if
--   $$e^H_C=\frac{\mu\{2\theta-\rho[1-(1-\alpha)^2\lambda]\}}{\Xi},\qquad e^H_E=\frac{(1-\alpha)\mu\{\lambda[2-(1-\alpha)^2\rho]+\rho\}}{\Xi}.$$
--
--   In particular the in-house equilibrium exists and is unique. These are the solutions of the first-order conditions (8) and (9); the statement includes that they are the global maximizer on the non-negative quadrant.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), p. 3187 (PDF 7), eqs. (8), (9); p. 3195 (PDF 15), Appendix A, eqs. (A.1), (A.2)

import Mathlib
import Definitions.Def_BrandLicensing_Intensive_Model

namespace BrandLicensing.Intensive

/-- (8), (9), (A.1), (A.2), pp. 3187, 3195: the in-house optimum exists, is unique, and is given
by (A.1)–(A.2). -/
theorem eq_A1_A2_inHouse_eq (P : Params) (hP : P.Standing) (eC eE : ℝ) :
    IsInHouseEq P eC eE ↔ eC = eCH_cf P ∧ eE = eEH_cf P := by sorry
end BrandLicensing.Intensive
