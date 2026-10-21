-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_eq_12
-- name    : CropMSP.MarketUnc.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:04.790267+00:00
-- url     : https://prove2.me/theorems/407b7ed5-a0c5-4312-8e7e-d68a7b8d3f7b
-- title:
--   Eq. (12), p. 12 — consumer surplus under linear inverse demand
-- statement:
--   At equilibrium quantity $q=\tau(m)$, consumer surplus is the area between inverse demand and the realized market price. With slope minus one, the shock cancels from that area and
--
--   $$C(m)=\int_0^{\tau(m)}\bigl(\tau(m)-x\bigr)\,dx=\frac{\tau(m)^2}{2}.$$
--
--   This term distinguishes net social value from the farmer-only net benefit.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 12, eq. (12)

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem eq_12 (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) :
    consumerSurplus P q = (tau P m) ^ 2 / 2 := by sorry

end CropMSP.MarketUnc
