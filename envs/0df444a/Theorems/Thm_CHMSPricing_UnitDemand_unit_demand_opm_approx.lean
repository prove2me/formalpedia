-- Prove2me | Theorems.Thm_CHMSPricing_UnitDemand_unit_demand_opm_approx
-- name    : CHMSPricing.UnitDemand.unit_demand_opm_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:55:16.494196+00:00
-- url     : https://prove2.me/theorems/569ab4c5-f63f-4133-b3f0-5d91adb1fb69
-- title:
--   Theorem 14, p. 9 — a truthful 6.75-approximate posted-price menu for unit-demand buyers of multiple copies of multiple items
-- statement:
--   Consider an instance of the BMUMD in which the seller has $\mathrm{cap}(k)$ copies of each item $k$ of a finite set $K$ on sale, there are $m$ unit-demand buyers, and buyer $i$ has a value $v_{(i,k)}$ for item $k$, the values being independent with regular distributions $F_{(i,k)}$. The feasible allocations give each buyer at most one item and use at most $\mathrm{cap}(k)$ copies of item $k$.
--
--   Then there are prices $p = (p_{(i,k)})$ such that for every arrival order $\sigma$ of the buyers the order-oblivious price-menu mechanism $\mathcal P_\sigma$ with prices $p$ is truthful and individually rational, and
--   $$\mathcal R^{\mathcal A} \le 6.75 \cdot \mathcal R^{\mathcal P_\sigma}$$
--   for every individually rational, truthful deterministic mechanism $\mathcal A$ for the instance.
--
--   This covers the hotel-rooms example of the introduction: rooms of several types in several copies sold to unit-demand guests by posting a menu of prices, within a constant factor of the optimal revenue of any deterministic truthful mechanism.
--
--   **Formalization Note** "$6.75$-approximate OPM" is spelled out: one set of prices, for every arrival order, a truthful mechanism, and the factor $27/4$ against every deterministic truthful individually rational mechanism (the benchmark of Theorem 4). The last sentence of the paper's theorem, that the prices can be computed in polynomial time, is not formalized: it is an algorithmic claim with no cost model here. Regularity of the distributions is added: the theorem follows from Theorem 13, whose proof is given for regular distributions, the non-regular case being only sketched with randomized prices (App. E). Distributions follow pin P1. Ties in a buyer's choice are broken by a fixed rule, which has probability zero of mattering.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 9, §6.1, Theorem 14 (from Theorems 4 and 13)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_MenuMech

namespace CHMSPricing.UnitDemand

/-- Theorem 14, p. 9: `m` unit-demand buyers, items `K` with `cap k` copies of item `k`, and
independent regular values `v_{(i,k)} ∼ F_{(i,k)}` of each buyer for each item. There are prices
`p` such that, for every arrival order `σ`, the order-oblivious price-menu mechanism with prices
`p` is truthful and `6.75`-approximates the revenue of every deterministic truthful individually
rational mechanism. -/
theorem unit_demand_opm_approx {m : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (cap : K → ℕ) (D : Fin m × K → ValueDist) (hreg : ∀ j, (D j).Regular) :
    ∃ p : Fin m × K → ℝ, ∀ σ : Equiv.Perm (Fin m),
      IsTruthfulMulti D (unitDemandSystem cap) Prod.fst
        (menuMech (unitDemandSystem cap) Prod.fst σ p) ∧
      ∀ A : MultiMechanism (Fin m × K) m,
        IsTruthfulMulti D (unitDemandSystem cap) Prod.fst A →
          revenueMulti D A ≤
            (27 / 4 : ℝ) * revenueMulti D (menuMech (unitDemandSystem cap) Prod.fst σ p) := by sorry

end CHMSPricing.UnitDemand
