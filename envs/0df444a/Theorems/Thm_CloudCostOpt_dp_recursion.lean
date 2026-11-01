-- Prove2me | Theorems.Thm_CloudCostOpt_dp_recursion
-- name    : CloudCostOpt.dp_recursion
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:05:22.080631+00:00
-- url     : https://prove2.me/theorems/9406aaaa-59c8-40fa-b114-3ecd30f2a6cb
-- title:
--   p.13 — the dynamic programming recursion of $\hat{\mathbb P}_i$ before the deadline
-- statement:
--   Let $f_i(s,l)$ be the optimal value of the single-order problem $\hat{\mathbb P}_i$ from order-state $(s,l)$, with $f_i(s,L_i)=0$, and $\tilde\beta_{i,j}=1-\beta_{i,j}$. Then:
--
--   1. for $l\le s<\delta_i$ and $0\le l\le L_i-1$,
--
--   $$
--   f_i(s,l)=\min_{j=0,\dots,J}\Big\{R_j+\beta_{i,j}\,f_i(s+1,l+1)+\tilde\beta_{i,j}\,f_i(s+1,l)\Big\};
--   $$
--
--   2. at the deadline, $f_i(\delta_i,l)=f^{Late}_i(l)=(L_i-l)\min_{j:\beta_{i,j}>0}(R_j+W_i)/\beta_{i,j}$ for $0\le l\le L_i-1$;
--   3. consequently $f_i(s,l)$ equals the value of the backward recursion started from $f^{Late}_i$, for all $l\le s$.
--
--   The recursion is how the paper computes $f_i$ and the optimal resources $j^*(i,s,l)$ used by $\hat\pi$.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types and Lᵢ ≥ 1 steps, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing); reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1)
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - encoding: the minimum expected remaining cost over all ways of processing the order → infimum over deterministic strategies that are functions of the past step outcomes, with i.i.d. uniform step trials; reason: Lean convention for the single-order control problem; the outcome history is all the controller observes
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - encoding: min_j (R_j + Wᵢ)/β_{i,j} over all j (the dummy gives Wᵢ/0 = +∞) → minimum over {j : β_{i,j} > 0}; reason: in Lean x/0 = 0; the excluded terms are +∞ on the page, so the minimum is the same
--   - reading: fᵢ(s, l) denotes both the minimum expected remaining cost and the quantity computed by the recursion → the Bellman equation for the optimal value, and its equality with the recursion values fDP, as separate clauses; reason: the page uses one symbol for both; the identification is what "the definition of fᵢ(s, l) implies the following recursion" asserts
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §3, p.13

import Mathlib
import Definitions.Def_CloudCostOpt_orderValue
import Definitions.Def_CloudCostOpt_fDP
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **The dynamic programming recursion of `ℙ̂ᵢ`** (p.13): for `l ≤ s < δᵢ` and `0 ≤ l ≤ Lᵢ − 1`,
`fᵢ(s, l) = min_j {R_j + β_{i,j} fᵢ(s + 1, l + 1) + β̃_{i,j} fᵢ(s + 1, l)}`, where
`fᵢ(δᵢ, l) = f^Late_i(l)`, `0 ≤ l ≤ Lᵢ − 1`.  Consequently the optimal values of `ℙ̂ᵢ` are the
recursion values `fDP` (for all `l ≤ s`).

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §3, p.13.

Formalization Note: the minimum ranges over all `j`, including the dummy resource `0`. -/
theorem dp_recursion (S : System) (hS : Standing S) (i : Fin S.I) :
    (∀ s l, l ≤ s → s < S.δ i → l < S.L i →
      orderValue S i s l = ⨅ j : Fin (S.J + 1),
        (ENNReal.ofReal (resCost S j) +
          ENNReal.ofReal (S.β i j) * orderValue S i (s + 1) (l + 1) +
          ENNReal.ofReal (1 - S.β i j) * orderValue S i (s + 1) l)) ∧
    (∀ l, l < S.L i →
      orderValue S i (S.δ i) l = ENNReal.ofReal (((S.L i : ℝ) - l) * lateRatio S i)) ∧
    (∀ s l, l ≤ s → orderValue S i s l = ENNReal.ofReal (fDP S i s l)) := by sorry

end CloudCostOpt
