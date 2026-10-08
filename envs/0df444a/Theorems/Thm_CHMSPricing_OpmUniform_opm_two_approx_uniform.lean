-- Prove2me | Theorems.Thm_CHMSPricing_OpmUniform_opm_two_approx_uniform
-- name    : CHMSPricing.OpmUniform.opm_two_approx_uniform
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:56:26.865209+00:00
-- url     : https://prove2.me/theorems/307983c0-d3ec-4af3-8e55-03014aac907d
-- title:
--   Theorem 10, p. 9 — under a uniform matroid, order-oblivious posted prices 2-approximate the optimal revenue
-- statement:
--   Consider $n$ agents with independent values $v_i \sim F_i$, each distribution with a density and regular, and a seller with $k$ identical units: the feasibility constraint is the $k$-uniform matroid, in which a set of agents can be served if and only if it has at most $k$ members.
--
--   For prices $\mathbf p$, the order-oblivious revenue estimate is
--   $$\mathcal R^{\mathrm{obl}}_{\mathbf p} = \mathbb E_{\mathbf v}\ \min_{S \in \mathcal S_{\mathbf v}} \sum_{i \in S} p_i,$$
--   where $\mathcal S_{\mathbf v}$ is the class of maximal feasible sets of agents with $v_i \ge p_i$: the revenue guaranteed against an adversary who, knowing the values, picks the least profitable maximal set of buyers to serve.
--
--   **Theorem.** There exist prices $\mathbf p$ such that every truthful mechanism $M$ for this instance satisfies
--   $$\mathcal R^{M} \le 2\, \mathcal R^{\mathrm{obl}}_{\mathbf p}.$$
--   Since Myerson's mechanism is a truthful mechanism of maximal revenue (Theorem 19), this says that $\mathcal R^{\mathrm{obl}}_{\mathbf p}$ 2-approximates $\mathcal R^{\mathcal M}$: posted prices that do not depend on the order in which buyers arrive lose at most half of the optimal revenue.
--
--   **Formalization Note** $\mathcal R^{\mathcal M}$ is not constructed; the bound is stated against every truthful (dominant-strategy incentive compatible, ex-post individually rational, measurable, integrable-payment) mechanism, with the prices chosen before the mechanism ("there exist prices for all mechanisms"). Prices are arbitrary reals and may lie outside the supports. Distributions are pinned to bounded supports with positive densities, and are regular as in the paper's proof. No hypothesis on $k$ is needed.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 9, §5.2, Theorem 10 (proof: App. D.2, pp. 18–19)

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_Mechanism
import Definitions.Def_CHMSPricing_OpmUniform_Opm

namespace CHMSPricing.OpmUniform

theorem opm_two_approx_uniform {n : ℕ} (D : Fin n → ValueDist) (hreg : ∀ i, (D i).Regular)
    (k : ℕ) :
    ∃ p : Fin n → ℝ, ∀ M : Mechanism (Fin n), IsTruthful D (uniformSystem n k) M →
      revenue D M ≤ 2 * oblRevenue D (uniformSystem n k) p := by sorry

end CHMSPricing.OpmUniform
