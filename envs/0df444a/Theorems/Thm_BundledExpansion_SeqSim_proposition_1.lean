-- Prove2me | Theorems.Thm_BundledExpansion_SeqSim_proposition_1
-- name    : BundledExpansion.SeqSim.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:12.980723+00:00
-- url     : https://prove2.me/theorems/4b46faf4-5885-4491-9b33-acfcfe8b5286
-- title:
--   Proposition 1, p. 14 — unique fixed-cost threshold
-- statement:
--   There is exactly one threshold $\bar\beta\in(1,2)$ at which the two optimal policy classes have equal total cost. For each admissible multiplier $\beta\in[1,2]$,
--
--   $$
--   V_{\mathrm{sim}}(\beta)\le V_{\mathrm{seq}}\iff\beta\le\bar\beta,
--   \qquad
--   V_{\mathrm{sim}}(\beta)<V_{\mathrm{seq}}\iff\beta<\bar\beta.
--   $$
--
--   Thus joint replenishment has lower cost below the threshold, while sequential replenishment has lower cost above it. Equality is included at the threshold, as the paper’s own explanation states. **Formalization Note** The result assumes continuous demand and a strict pointwise demand-ratio guard in addition to the standing model conditions. The guard is needed: without it, a feasible joint expansion can exist while the corresponding two-expansion sequential policy violates Assumption 1. Both optima are real infima over complete admissible policy classes, and Lean indices 0 and 1 are the paper’s 1 and 2.
-- source:
--   Arbabian, Chen & Moinzadeh, Capacity Expansions with Bundled Supplies of Attributes, SSRN 3085349 (manuscript of April 14, 2019), https://ssrn.com/abstract=3085349, p. 14 (PDF 15), Proposition 1

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim

theorem proposition_1 (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    ∃! βbar : ℝ, 1 < βbar ∧ βbar < 2 ∧
      ∀ β ∈ Set.Icc (1 : ℝ) 2,
        (optSim P β ≤ optSeq P ↔ β ≤ βbar) ∧
        (optSim P β < optSeq P ↔ β < βbar) := by sorry

end BundledExpansion.SeqSim
