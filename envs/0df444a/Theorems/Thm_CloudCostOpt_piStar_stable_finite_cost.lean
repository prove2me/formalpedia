-- Prove2me | Theorems.Thm_CloudCostOpt_piStar_stable_finite_cost
-- name    : CloudCostOpt.piStar_stable_finite_cost
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:45:21.558276+00:00
-- url     : https://prove2.me/theorems/2af0cdd4-0a91-4cc0-832d-cf0f0c3aebd1
-- title:
--   The newsvendor policy $\pi^*$ is stable and has finite cost (no sign assumption on $M^{\pi^*}_j$)
-- statement:
--   For every instance satisfying the standing assumptions, positive arrival rates $\lambda_i>0$, $0<R_j<V_j$ and every selection $j^*$ of optimal resources, the policy $\pi^*$ (assignments of $\hat\pi$, reservation $M_j=(\mu_j+z_j\sqrt{\mu_j})^+$, on-demand capacity $m_{j,t}=(u_{j,t}-M_j)^+$) is stable and
--
--   $$
--   f^{\pi^*}<\infty .
--   $$
--
--   No sign assumption on $\mu_j+z_j\sqrt{\mu_j}$ is made: where it is negative the reservation is $0$.
--
--   Role: clause 2 of Corollary 6; it gives $OPT\le f^{\pi^*}<\infty$ for every demand scale $\theta>0$, including the scales at which $M^{\pi^*}_j\ge0$ fails and the exact cost formula (11) does not apply.
--
--   **Formalization Note**: stability and cost are the platform definitions `IsStable` and `avgCost` (liminf of Cesaro averages of expected period costs in $[0,\infty]$).
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, https://ssrn.com/abstract=4166245, Corollary 6 (2), p.18, with the definition of pi* (Section 4, pp.16-17) and the Note on p.16 (M_j = (mu_j + z_j sqrt(mu_j))^+)

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

theorem piStar_stable_finite_cost (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i)
    (hR : ∀ j, 0 < S.R j) (hRV : ∀ j, S.R j < S.V j) :
    IsStable S lam (piStar S sel lam) ∧ avgCost S S.R S.V lam (piStar S sel lam) < ⊤ := by sorry

end CloudCostOpt
