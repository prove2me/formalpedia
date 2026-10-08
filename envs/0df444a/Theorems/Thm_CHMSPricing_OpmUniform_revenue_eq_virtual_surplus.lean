-- Prove2me | Theorems.Thm_CHMSPricing_OpmUniform_revenue_eq_virtual_surplus
-- name    : CHMSPricing.OpmUniform.revenue_eq_virtual_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:55:49.768209+00:00
-- url     : https://prove2.me/theorems/3b0be6bf-086b-419c-9a80-732769ed26dc
-- title:
--   Proposition 1, p. 5 — the expected revenue of a truthful mechanism equals its expected virtual surplus
-- statement:
--   Let agents $i \in \iota$ (a finite set) have independent values $v_i \sim F_i$, each $F_i$ with a density and regular (its virtual valuation $\phi_i(x) = x - (1-F_i(x))/f_i(x)$ is non-decreasing). Let $\mathcal J$ be a downward-closed feasibility constraint and $M$ a truthful (dominant-strategy incentive compatible, ex-post individually rational) mechanism respecting $\mathcal J$, normalized so that an agent with the lowest possible value $\underline v_i$ gets zero utility whatever the other agents report. Then
--   $$\mathbb E_{\mathbf v}\Big[\sum_i \pi_i(\mathbf v)\Big] = \mathbb E_{\mathbf v}\Big[\sum_{i \in M(\mathbf v)} \phi_i(v_i)\Big],$$
--   that is, the expected revenue of $M$ equals its expected virtual surplus $\mathbb E[\Phi(M(\mathbf v), \mathbf v)]$.
--
--   This is Myerson's characterization of revenue, and it is how the revenues of Myerson's mechanism and of the posted-price mechanism are compared in the proof of Theorem 10.
--
--   **Formalization Note** The identity needs the normalization that the lowest type has zero utility; without it a truthful mechanism could pay every agent a constant. The paper presupposes it on p. 12 ("These are uniquely determined by the allocation rule assuming that agents that are not served pay nothing"). It is a hypothesis here, disclosed. Distributions are pinned to bounded supports with positive densities.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, §2.3, Proposition 1 (restated p. 12)

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Mechanism

namespace CHMSPricing.OpmUniform

open MeasureTheory

theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular) (J : SetSystem ι) (M : Mechanism ι)
    (hM : IsTruthful D J M)
    (hnorm : ∀ v ∈ typeSpace D, ∀ i,
      M.utility i (D i).lo (Function.update v i (D i).lo) = 0) :
    revenue D M = ∫ v, virtualSurplus D (M.alloc v) v ∂(prior D) := by sorry

end CHMSPricing.OpmUniform
