-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_beta_one
-- name    : BundledExpansion.SeqSim.beta_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:11.432498+00:00
-- url     : https://prove2.me/theorems/4a64b899-077e-4277-b2e9-ab1b07e24ee2
-- title:
--   Proposition 1, β = 1 — simultaneous is cheaper
-- statement:
--   At the joint fixed-cost multiplier $\beta=1$, the optimal simultaneous-replenishment cost is strictly less than the optimal sequential-replenishment cost:
--
--   $$
--   V_{\mathrm{sim}}(1)<V_{\mathrm{seq}}.
--   $$
--
--   This supplies the lower endpoint of the policy threshold. **Formalization Note** Both optima are infima over all admissible policies, without assuming they are attained. Continuous demand and the strict demand-ratio guard are added to the paper’s standing model conditions. Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 14 (PDF 15), paragraph following Proposition 1

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem beta_one (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    optSim P 1 < optSeq P := by sorry

end BundledExpansion.SeqSim
