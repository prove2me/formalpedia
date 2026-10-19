-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_beta_two
-- name    : BundledExpansion.SeqSim.beta_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:13.612074+00:00
-- url     : https://prove2.me/theorems/cee01512-2f8b-4f92-a957-e5dc88050df9
-- title:
--   Proposition 1, β = 2 — sequential is cheaper
-- statement:
--   At the joint fixed-cost multiplier $\beta=2$, the optimal sequential-replenishment cost is strictly less than the optimal simultaneous-replenishment cost:
--
--   $$
--   V_{\mathrm{seq}}<V_{\mathrm{sim}}(2).
--   $$
--
--   This supplies the upper endpoint of the policy threshold. **Formalization Note** The cost values are infima over the complete policy classes; their attainment is a proof obligation, not a premise. Continuous demand and the strict demand-ratio guard are added to the paper’s standing model conditions. Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 14 (PDF 15), paragraph following Proposition 1

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem beta_two (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    optSeq P < optSim P 2 := by sorry

end BundledExpansion.SeqSim
