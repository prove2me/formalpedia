-- Prove2me | Theorems.Thm_FalseFailureReturns_TargetRebate_coord_effort_gt_one
-- name    : FalseFailureReturns.TargetRebate.coord_effort_gt_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:37:33.874315+00:00
-- url     : https://prove2.me/theorems/dc8e558a-fd41-4b92-b517-42e340414485
-- title:
--   §3, p. 382: in the interesting case, $\rho^C > 1$
-- statement:
--   Let $a > 0$, $\beta > 0$, $M_m > 0$ and $R_r > 0$ be as in the model. Suppose the total potential saving of avoiding false failures exceeds the marginal cost of the minimum effort level,
--   $$(M_m + R_r)\,\beta > a.$$
--   Then the coordinated effort exceeds the minimum effort level:
--   $$\rho^C = \Big[\frac{M_m + R_r}{a}\,\beta\Big]^{1/3} > 1.$$
--
--   This is the "interesting case" of the paper, in which the coordinated supply chain exerts more than the minimum effort; every later result about coordinating contracts is stated in it.
--
--   **Formalization Note** The paper writes the condition as $(m + r)\beta > a$. That condition does not imply $\rho^C > 1$ when $\delta_m(w - c) + \delta_r(p - w) < 0$; the condition the conclusion rests on is $(M_m + R_r)\beta > a$, which is used here.
-- source:
--   Ferguson, Guide & Souza, Supply Chain Coordination for False Failure Returns, MSOM 8(4) 2006, p. 382, §3

import Mathlib
import Definitions.Def_FalseFailureReturns_TargetRebate_Model

namespace FalseFailureReturns.TargetRebate

theorem coord_effort_gt_one (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) :
    1 < coordEffort P := by sorry

end FalseFailureReturns.TargetRebate
