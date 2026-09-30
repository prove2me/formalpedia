-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_decentr_le_coord
-- name    : FalseFailureReturns.TargetRebate.decentr_le_coord
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:38:22.969001+00:00
-- url     : https://prove2.me/theorems/bfc3b820-b58e-4bc2-bb66-fa3835142adf
-- title:
--   §3, p. 382: $\rho^C \ge \rho^D$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$, $R_r > 0$, and assume the interesting case $(M_m + R_r)\beta > a$. Then the decentralized effort does not exceed the coordinated effort:
--   $$\rho^D = \max\Big\{\Big(\frac{R_r\beta}{a}\Big)^{1/3},\,1\Big\} \;\le\; \rho^C = \Big[\frac{M_m + R_r}{a}\,\beta\Big]^{1/3}.$$
--
--   Without a contract the retailer under-invests in effort; the comparison is used in the appendix proof of Proposition 2.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 382, §3

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model

namespace FalseFailureReturns.TargetRebate

theorem decentr_le_coord (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) :
    decentrEffort P ≤ coordEffort P := by sorry

end FalseFailureReturns.TargetRebate
