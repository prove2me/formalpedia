-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_eq_10
-- name    : CropMSP.MarketUnc.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:29.552011+00:00
-- url     : https://prove2.me/theorems/11a9ac36-173e-4de1-ba8e-18176626097d
-- title:
--   Eq. (10), p. 11 — farmer surplus under an admissible MSP
-- statement:
--   Let $m$ be an admissible minimum support price with equilibrium quantity $q=\tau(m)$. The expected aggregate farmer surplus, obtained by integrating expected effective sale price minus cultivation cost over the participating farmers, is
--
--   $$F(m)=\frac{\tau(m)}4\left[\frac{(m-(a-\tau(m))+\theta)^2}{\theta}+2(2a-3\tau(m))\right].$$
--
--   This explicit surplus formula is one input to the net benefit and net social value calculations.
--
--   **Formalization Note** The definition of $F$ integrates over the actual set of sowers rather than building $\tau(m)$ into it. Theorem 1 identifies that set up to a null boundary point.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 11, eq. (10)

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem eq_10 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    farmerSurplus P m q =
      tau P m / 4 *
        (((m - (P.a - tau P m) + P.θ) ^ 2) / P.θ + 2 * (2 * P.a - 3 * tau P m)) := by sorry

end CropMSP.MarketUnc
