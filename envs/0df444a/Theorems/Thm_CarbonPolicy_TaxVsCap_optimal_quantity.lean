-- Prove2me | Theorems.Thm_CarbonPolicy_TaxVsCap_optimal_quantity
-- name    : CarbonPolicy.TaxVsCap.optimal_quantity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T01:07:13.617424+00:00
-- url     : https://prove2.me/theorems/de5626d8-7fab-4334-a8cd-1667148798cf
-- title:
--   Equation (1): optimal second-stage production
-- statement:
--   For a positive demand sensitivity $b$, fixed emission intensity $\gamma$, realized market potential $a$, permit price $k$, and quota $w$, the firm's operating profit is maximized over all real production quantities by
--
--   $$q^*(\gamma,a,k)=\frac{a-\gamma k}{2b}.$$
--
--   This identifies the second-stage response used in both first-stage policy objectives.
--
--   **Formalization Note** The maximization is over all real $q$, as in the paper's unconstrained $\max_q$.
-- source:
--   Fan, Chen, Chen, Is Price Commitment a Better Solution to Control Carbon Emissions and Promote Technology Investment?, SSRN 3817235 (version of November 15, 2021), p. 12, equation (1)

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting

open ProbabilityTheory MeasureTheory

namespace CarbonPolicy.TaxVsCap

theorem optimal_quantity (b w γ a k : ℝ) (hb : 0 < b) :
    ∀ q : ℝ, profit b w γ a k q ≤ profit b w γ a k (qStar b γ a k) := by sorry

end CarbonPolicy.TaxVsCap
