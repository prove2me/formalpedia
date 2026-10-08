-- Prove2me | Theorems.Thm_CHMSPricing_SpmMatroid_revenue_eq_virtual_surplus
-- name    : CHMSPricing.SpmMatroid.revenue_eq_virtual_surplus
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:40:37.068986+00:00
-- url     : https://prove2.me/theorems/50c0f447-f3ea-4dac-b76b-5d83a3e38973
-- title:
--   Proposition 1, p. 5 — with regular distributions, expected revenue equals expected virtual surplus
-- statement:
--   Let $n$ single-parameter agents have independent values $v_i \sim F_i$ with regular distributions, and let $\mathcal J$ be a downward-closed feasibility constraint. Let $M$ be a truthful mechanism, normalized so that an agent with the lowest possible value $\underline v_i$ obtains zero utility whatever the others report. Then
--
--   $$\mathbb E_{\mathbf v}\Big[\sum_i \pi_i(\mathbf v)\Big] = \mathbb E_{\mathbf v}\big[\Phi(M(\mathbf v), \mathbf v)\big] = \mathbb E_{\mathbf v}\Big[\sum_{i \in M(\mathbf v)} \phi_i(v_i)\Big].$$
--
--   This is Myerson's characterization of revenue, the basis of the optimal mechanism and of the upper bound of Lemma 2.
--
--   **Formalization Note** The normalization $u_i(\underline v_i; (\underline v_i, \mathbf v_{-i})) = 0$ is added: without it a truthful mechanism could pay every agent a constant and break the identity. The paper fixes the payments by "assuming that agents that are not served pay nothing" (p. 12); the normalization is the standard form of that convention. Distributions follow the bounded-support density model of the definitions.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 5, Proposition 1 (restated p. 12)

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_Mechanism

namespace CHMSPricing.SpmMatroid

open MeasureTheory

/-- Proposition 1 (p. 5): with regular value distributions, the expected revenue of a truthful
mechanism equals its expected virtual surplus `𝔼_v[Φ(M(v), v)]`, under the normalization that
an agent with the lowest value `loᵢ` gets zero utility (p. 12: payments "uniquely determined
by the allocation rule assuming that agents that are not served pay nothing"). -/
theorem revenue_eq_virtual_surplus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → ValueDist) (hreg : ∀ i, (D i).Regular)
    (J : SetSystem ι) (M : Mechanism ι) (hM : IsTruthful D J M)
    (hnorm : ∀ v ∈ typeSpace D, ∀ i,
      M.utility i (D i).lo (Function.update v i (D i).lo) = 0) :
    revenue D M = ∫ v, virtualSurplus D (M.alloc v) v ∂(prior D) := by sorry

end CHMSPricing.SpmMatroid
