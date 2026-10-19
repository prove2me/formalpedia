-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_eq_81
-- name    : DERAggregation.MarketPower.eq_81
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:59.523505+00:00
-- url     : https://prove2.me/theorems/0729addb-82d5-4fc9-8f43-84cf32f26731
-- title:
--   (81), §5.2.2, p. 32 — the per-generator supply at every strategic outcome without participation
-- statement:
--   Consider the single-node market of §5 without prosumer participation and with strategic generators, under Assumption 5. Let $(q,\lambda,d)$ be any strategic outcome: a symmetric pure equilibrium of the quantity game (75) in which each generator supplies $q$ and the market clears at total $Nq$ with price $\lambda$ and purchases $d$. Then $q>0$ and
--   $$q=y^{SN}_j=\frac{\sum_{\{i\,:\,d_i>0\}}\Big(\frac{\alpha-b_i}{2a_i}-C_i\Big)}{N+1}. \tag{81}$$
--
--   The active prosumers $\{i:d_i>0\}$ are exactly those counted by the paper's indicator $\mathbb 1\{Ny^{SN}_j>y^i\}$, by Lemma 7 and (78).
--
--   **Formalization Note** The indicator $\mathbb 1\{Ny^{SN}_j>y^i\}$ with the sorted thresholds $y^i$ of (77) is written through the set of prosumers with positive purchase, which is the paper's own equivalence (Lemma 7, (78)). The paper does not show that such an outcome exists, and none is claimed here: the statement is about every strategic outcome. The bid layer (Lemma 8) is not modelled. Assumption 5 includes the readings H1, H2 of its informal clauses.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.2.2, p. 32, (75)–(81)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- (81), §5.2.2, p. 32. Under Assumption 5, at every strategic outcome without participation
(a symmetric pure equilibrium of the quantity game (75)) each generator's supply is positive and
satisfies `y^{SN}_j = Σ_{i : d_i > 0} ((α − b_i)/(2a_i) − C_i) / (N + 1)`, where the prosumers
with `d_i > 0` are those of the indicator `1{N y^{SN}_j > y^i}` (Lemma 7, (78)). -/
theorem eq_81 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) (q lam : ℝ) (d : ι → ℝ) (h : IsStratN a b C α N q lam d) :
    0 < q ∧
      q = (∑ i ∈ univ.filter (fun i => 0 < d i), ((α - b i) / (2 * a i) - C i)) /
        ((N : ℝ) + 1) := by sorry

end DERAggregation.MarketPower
