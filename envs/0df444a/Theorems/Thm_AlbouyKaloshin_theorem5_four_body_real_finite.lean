-- Prove2me | Theorems.Thm_AlbouyKaloshin_theorem5_four_body_real_finite
-- name    : AlbouyKaloshin.theorem5_four_body_real_finite
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T21:44:35.348995+00:00
-- url     : https://prove2.me/theorems/a79f941c-0912-4eae-aadc-2f24f7efc6d6
-- title:
--   Theorem 5: four bodies, finitely many real normalized central configurations
-- statement:
--   Let $m_1,m_2,m_3,m_4>0$. Then there are finitely many real normalized central configurations of four bodies: solutions $(x,y,\delta)$ of system (4) with all coordinates $x_k,y_k$ real. The inverse distances $\delta_{kl}=\pm(x_{kl}^2+y_{kl}^2)^{-1/2}$ are not required to be positive.
--
--   This contains Theorem 1 (Hampton–Moeckel) and also excludes continua of real configurations with mutual distances of either sign.
-- source:
--   A. Albouy and V. Kaloshin, Finiteness of central configurations of five bodies in the plane, Annals of Mathematics 176 (2012), no. 1, 535–588, https://doi.org/10.4007/annals.2012.176.1.10, p. 563, Theorem 5 (real normalized central configurations: Definition 2, p. 540)

import Mathlib
import Definitions.Def_AlbouyKaloshin_CentralConfigurations

namespace AlbouyKaloshin

theorem theorem5_four_body_real_finite (m : Fin 4 → ℝ) (hm : ∀ k, 0 < m k) :
    (RealNormalizedCC 4 (fun k => (m k : ℂ))).Finite := by sorry

end AlbouyKaloshin
