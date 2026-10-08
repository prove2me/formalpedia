-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_sum_servProb_le_rank
-- name    : CHMSPricing.SpmPartition.sum_servProb_le_rank
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T11:43:42.043402+00:00
-- url     : https://prove2.me/theorems/50b681d7-664c-4607-a8f6-1f3aed38ec8a
-- title:
--   §4, p. 6 — the service probabilities of a truthful mechanism satisfy Σ_{i∈S} q^M_i ≤ rank(S)
-- statement:
--   Let $M$ be a truthful mechanism for a downward-closed feasibility constraint $\mathcal J$, and let $q^M_i$ be the probability that $M$ serves agent $i$. Then for every set $S$ of agents
--
--   $$
--   \sum_{i\in S}q^M_i\le\operatorname{rank}(S),
--   $$
--
--   where $\operatorname{rank}(S)$ is the size of a largest feasible subset of $S$.
--
--   For a partition matroid with part $S=\{i:\mathrm{part}(i)=b\}$ of capacity $\mathrm{cap}(b)$ this gives $\sum_{i\in S}q^M_i\le\mathrm{cap}(b)$, the constraint on the probabilities used in Appendix C.2 ($\sum_i q_i\le 1$ for one unit, $\sum_i q_i/k\le1$ for $k$ units).
--
--   **Formalization Note** The page states the chain $\sum_{i\in S}q_i\le\sum_{i\in S}q^M_i\le\operatorname{rank}(S)$; with densities $q_i=q^M_i$, so only the second inequality is stated. Only feasibility and measurability of $M$ are used, but the hypothesis is the full truthfulness bundle, matching the page's setting. Values: each value distribution $F_i$ is given by a density $f_i$ that is measurable and strictly positive on a bounded interval $[\underline v_i,\bar v_i]$ with $0\le\underline v_i<\bar v_i$, integrates to $1$ there and puts no mass outside (the paper says only "distribution function $F_i$ with density $f_i$").
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 6, §4 (paragraph defining the mechanism S: "Then, by definition, Σ_{i∈S} q_i ≤ Σ_{i∈S} q^M_i ≤ rank(S)")

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism

namespace CHMSPricing.SpmPartition

theorem sum_servProb_le_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (S : Finset ι) :
    ∑ i ∈ S, servProb D M i ≤ (J.rank S : ℝ) := by sorry

end CHMSPricing.SpmPartition
