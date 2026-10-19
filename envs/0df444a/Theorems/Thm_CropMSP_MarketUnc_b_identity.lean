-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_b_identity
-- name    : CropMSP.MarketUnc.b_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:08.638685+00:00
-- url     : https://prove2.me/theorems/7564ebcb-e249-4011-9132-e75f3ce13905
-- title:
--   Proof of Proposition 1, p. 39 — net benefit identity
-- statement:
--   For an admissible minimum support price $m$ at equilibrium quantity $q=\tau(m)$, farmer surplus less implementation expenditure simplifies to
--
--   $$B(m)=F(m)-E(m)=\tau(m)\left(a-\frac32\tau(m)\right).$$
--
--   The identity reduces the sign and maximization claims for net benefit to a function of equilibrium production.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 39, proof of Proposition 1

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem b_identity (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    netBenefit P m q = tau P m * (P.a - 3 / 2 * tau P m) := by sorry

end CropMSP.MarketUnc
