-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_sum_servProb_le_rank
-- name    : CHMSPricing.SpmMatroid.sum_servProb_le_rank
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:40:47.415977+00:00
-- url     : https://prove2.me/theorems/e657aa78-79f6-49cb-a367-92ad3c304c14
-- title:
--   §4, p. 6 — service probabilities are bounded by rank: Σ_{i∈S} q^M_i ≤ rank(S)
-- statement:
--   Let $M$ be a mechanism whose allocation is feasible for a downward-closed constraint $\mathcal J$ at every value profile of the type space, with measurable service events, and let $q^M_i$ be the probability that $M$ serves agent $i$ when $v_i \sim F_i$ independently. Then for every set $S$ of agents
--
--   $$\sum_{i \in S} q^M_i \le \operatorname{rank}(S).$$
--
--   This is the only property of $M$'s service probabilities that the analysis of the SPM uses.
--
--   **Formalization Note** Only feasibility and measurability of $M$ are assumed (truthfulness is not needed). The paper's first inequality $\sum_{i\in S} q_i \le \sum_{i\in S} q^M_i$ is an equality in the regular case $q_i = q^M_i$ and is not stated.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 6, §4, last sentence of the paragraph defining 𝒮

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

namespace CHMSPricing.SpmMatroid

/-- §4 (p. 6): for any mechanism whose allocation is feasible on the type space (with
measurable allocation events), `∑_{i ∈ S} q^M_i ≤ rank(S)` for every set `S` of agents. -/
theorem sum_servProb_le_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι)
    (hfeas : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v))
    (hmeas : ∀ i, MeasurableSet {v | i ∈ M.alloc v}) (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by sorry

end CHMSPricing.SpmMatroid
