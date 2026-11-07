-- Prove2me | Theorems.Thm_CloudCostOpt_piStar_zero_demand
-- name    : CloudCostOpt.piStar_zero_demand
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-06T17:46:30.082134+00:00
-- url     : https://prove2.me/theorems/591c69a7-2199-4b62-aa06-825b9e9802ac
-- title:
--   With zero demand the policy $\pi^*$ is stable and costs nothing
-- statement:
--   For every instance satisfying the standing assumptions and every selection $j^*$, scale the arrival rates by $\theta=0$ (all $\lambda_i=0$). Then no order ever arrives, $\mu_j=0$, $\pi^*$ reserves nothing and rents nothing, $\pi^*$ is stable and
--
--   $$
--   f^{\pi^*}(0)=0 .
--   $$
--
--   Role: the case $\theta=0$ of Corollary 6 (clauses 1-3): it gives $LB(0)=OPT(0)=f^{\pi^*}(0)=0$.
--
--   **Formalization Note**: $\mathrm{Poisson}(0)$ is the point mass at $0$, so the arrival counts vanish almost surely under the platform measure `sampleMeasure S 0`.
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, https://ssrn.com/abstract=4166245, Corollary 6, p.18 (demand scaled by theta >= 0; at theta = 0 the costs vanish), with the definition of pi* (Section 4, pp.16-17)

import Mathlib
import Definitions.Def_CloudCostOpt_piStar
import Definitions.Def_CloudCostOpt_avgCost
import Definitions.Def_CloudCostOpt_IsStable
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

theorem piStar_zero_demand (S : System) (hS : Standing S) (sel : Selection S) :
    IsStable S 0 (piStar S sel 0) ∧ avgCost S S.R S.V 0 (piStar S sel 0) = 0 := by sorry

end CloudCostOpt
