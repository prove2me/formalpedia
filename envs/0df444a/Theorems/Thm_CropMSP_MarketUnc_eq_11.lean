-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_eq_11
-- name    : CropMSP.MarketUnc.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:14.289096+00:00
-- url     : https://prove2.me/theorems/8511eae3-d9c3-4488-9eed-3090d913a4c0
-- title:
--   Eq. (11), p. 12 — MSP implementation expenditure
-- statement:
--   Let $m$ be an admissible minimum support price and $q=\tau(m)$ its equilibrium production quantity. Government expenditure is the quantity sold times the expected positive gap between the support price and the market price:
--
--   $$E(m)=\frac{\tau(m)}{4\theta}\bigl[m-(a-\tau(m)-\theta)\bigr]^2.$$
--
--   This identifies the fiscal cost subtracted from farmer surplus and consumer surplus in the policy metrics.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 12, eq. (11)

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem eq_11 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    expenditure P m q =
      tau P m / (4 * P.θ) * (m - (P.a - tau P m - P.θ)) ^ 2 := by sorry

end CropMSP.MarketUnc
