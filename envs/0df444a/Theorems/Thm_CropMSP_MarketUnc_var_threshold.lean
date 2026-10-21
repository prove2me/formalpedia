-- Prove2me | Theorems.Thm_CropMSP_MarketUnc_var_threshold
-- name    : CropMSP.MarketUnc.var_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:00.852489+00:00
-- url     : https://prove2.me/theorems/411133c7-54a1-41ba-9048-30e738535e02
-- title:
--   Eq. (6), p. 8, and proof of Theorem 1, p. 37 — VaR threshold with MSP
-- statement:
--   Fix a proposed crop quantity $q$, a minimum support price $m$, and a farmer with cost $c$. Under the paper's standing assumptions, the farmer's loss probability is at most $\alpha$ whenever $c<m$. For $m\le c$, the farmer finds the crop lucrative exactly when
--
--   $$c\le a-q-(1-2\alpha)\theta.$$
--
--   This threshold turns the individual VaR participation rule into the aggregate supply relation used to identify equilibrium.
--
--   **Formalization Note** The definition of lucrative uses weak inequalities in both the loss event and the probability bound, as in equations (1), (5), and (6). The MSP case is stated in the proof of Theorem 1 on p. 37; that proof writes strict inequalities, while the model rule uses weak ones.
-- source:
--   Chintapalli & Tang, The Value and Cost of Crop Minimum Support Price, SSRN 3681588 manuscript (Management Science 2021, doi:10.1287/mnsc.2020.3831), p. 8, eq. (6); p. 37, proof of Theorem 1

import Mathlib
import Definitions.Def_CropMSP_MarketUnc_Model

namespace CropMSP.MarketUnc

theorem var_threshold (P : Params) (hS : P.Standing) (m q c : ℝ) :
    (c < m → Lucrative P m q c) ∧
    (m ≤ c → (Lucrative P m q c ↔ c ≤ P.a - q - (1 - 2 * P.α) * P.θ)) := by sorry

end CropMSP.MarketUnc
