-- Prove2me | Theorems.Thm_CHMSPricing_SpmPartition_revenue_le_sum_price_mul_servProb
-- name    : CHMSPricing.SpmPartition.revenue_le_sum_price_mul_servProb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:43:40.599338+00:00
-- url     : https://prove2.me/theorems/fca39119-c6d3-41c0-92ce-be19296b69d9
-- title:
--   Lemma 2, p. 5 — the revenue of a truthful mechanism is at most Σ_i p^M_i q^M_i
-- statement:
--   Let agents $i$ have independent values $v_i\sim F_i$ with regular distributions, and let $\mathcal J$ be any downward-closed feasibility constraint. Let $M$ be a truthful mechanism for $\mathcal J$, let $q^M_i$ be the probability that $M$ serves agent $i$, and let $p^M_i=F_i^{-1}(1-q^M_i)$. Then
--
--   $$
--   \mathcal R^M\le\sum_i p^M_i\,q^M_i .
--   $$
--
--   The right-hand side is the revenue of offering each agent its own price $p^M_i$ while ignoring the feasibility constraint. It is the upper bound against which the sequential posted-price mechanism is compared.
--
--   **Formalization Note** Only the first paragraph of the paper's Lemma 2 (the regular case) is stated; the second paragraph (non-regular distributions, two randomized prices) is out of scope. Values: each value distribution $F_i$ is given by a density $f_i$ that is measurable and strictly positive on a bounded interval $[\underline v_i,\bar v_i]$ with $0\le\underline v_i<\bar v_i$, integrates to $1$ there and puts no mass outside (the paper says only "distribution function $F_i$ with density $f_i$"). A truthful mechanism here is deterministic, dominant-strategy incentive compatible on the type space $\prod_i[\underline v_i,\bar v_i]$, ex-post individually rational, feasible on the type space, with measurable allocation events and measurable, integrable payments; payments of unserved agents are not forced to be zero. The prices are not computed by an inverse distribution function: they are arguments $p_i\in[\underline v_i,\bar v_i]$ with $F_i(p_i)=1-q^M_i$, which determines $p_i$ uniquely because $F_i$ is continuous and strictly increasing on the support.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, Lemma 2 (first paragraph); proof in App. A, pp. 12–13

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem
import Definitions.Def_CHMSPricing_SpmPartition_Mechanism

namespace CHMSPricing.SpmPartition

theorem revenue_le_sum_price_mul_servProb {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (D i).lo (D i).hi ∧ (D i).cdf (p i) = 1 - servProb D M i) :
    revenue D M ≤ ∑ i, p i * servProb D M i := by sorry

end CHMSPricing.SpmPartition
