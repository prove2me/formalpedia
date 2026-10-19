-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_v_identity
-- name    : CropMSP.MarketUnc.v_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:06.021237+00:00
-- url     : https://prove2.me/theorems/6a794ff3-f642-44b6-a2e3-96d028b437b1
-- title:
--   Proof of Proposition 1, p. 40 — net social value identity
-- statement:
--   For an admissible minimum support price $m$ at equilibrium quantity $q=\tau(m)$, farmer and consumer surplus less implementation expenditure simplifies to
--
--   $$V(m)=F(m)+C(m)-E(m)=\tau(m)\bigl(a-\tau(m)\bigr).$$
--
--   Since $\tau(m)\le1<a$ under the standing assumptions, this formula supports the positivity and maximization claims for social value.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 40, proof of Proposition 1

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem v_identity (P : Params) (hS : P.Standing) (m q : ℝ)
    (heq : IsEquilibrium P m q) (hadm : Admissible P m q) :
    netSocialValue P m q = tau P m * (P.a - tau P m) := by sorry

end CropMSP.MarketUnc
