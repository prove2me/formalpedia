-- Prove2me | Theorems.Thm_CloudCostOpt_lemma_1_late_resource
-- name    : CloudCostOpt.lemma_1_late_resource
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:03:18.86434+00:00
-- url     : https://prove2.me/theorems/82189878-85b1-4a05-90e1-b10332d88dac
-- title:
--   Lemma 1 — a late order uses $\arg\min_j (R_j+W_i)/\beta_{i,j}$ in every period, and $f^{Late}_i(l)=(L_i-l)\min_j (R_j+W_i)/\beta_{i,j}$
-- statement:
--   Consider the single-order problem $\hat{\mathbb P}_i$, with optimal value $f_i(s,l)$ from order-state $(s,l)$. Let $c^{Late}_i=\min_{j:\beta_{i,j}>0}(R_j+W_i)/\beta_{i,j}$. For every late order-state, $s\ge\delta_i$ and $0\le l\le L_i-1$:
--
--   1. the optimal value is
--
--   $$
--   f_i(s,l)=f^{Late}_i(l)=(L_i-l)\,c^{Late}_i;
--   $$
--
--   2. a resource type $j$ is optimal in $(s,l)$, that is,
--
--   $$
--   R_j+W_i+\beta_{i,j}f_i(s+1,l+1)+\tilde\beta_{i,j}f_i(s+1,l)=f_i(s,l),
--   $$
--
--   if and only if $\beta_{i,j}>0$ and $(R_j+W_i)/\beta_{i,j}=c^{Late}_i$. This condition does not depend on $s$ or $l$: the optimal resource of a late order is the same in every period, $j^*(i,s,l)=j^{Late,*}_i=\arg\min_j(R_j+W_i)/\beta_{i,j}$.
--
--   Lemma 1 supplies the terminal condition of the dynamic program of p.13 and the late resource used by $\hat\pi$ and $\pi^*$.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types and Lᵢ ≥ 1 steps, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing); reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1)
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - encoding: the minimum expected remaining cost over all ways of processing the order → infimum over deterministic strategies that are functions of the past step outcomes, with i.i.d. uniform step trials; reason: Lean convention for the single-order control problem; the outcome history is all the controller observes
--   - encoding: expectations E[·] of nonnegative quantities → lower Lebesgue integrals ∫⁻ in [0, ∞]; reason: Lean convention; same values, and no junk 0 for a non-integrable quantity
--   - encoding: min_j (R_j + Wᵢ)/β_{i,j} over all j (the dummy gives Wᵢ/0 = +∞) → minimum over {j : β_{i,j} > 0}; reason: in Lean x/0 = 0; the excluded terms are +∞ on the page, so the minimum is the same
--   - reading: "the optimal resource-type to use … is j^{Late,*}_i := argmin_j (R_j + Wᵢ)/β_{i,j}" → j attains the Bellman equation at (s, l) iff j minimizes (R_j + Wᵢ)/β_{i,j} over {β_{i,j} > 0}; reason: "optimal resource" read as attaining the optimality equation; the iff states that the optimal set is the argmin set, for every tie-breaking
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 1, p.12

import Mathlib
import Definitions.Def_CloudCostOpt_orderValue
import Definitions.Def_CloudCostOpt_lateRatio
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Lemma 1** (p.12): for a late type-`i` order (`s ≥ δᵢ`, `0 ≤ l ≤ Lᵢ − 1`), in problem `ℙ̂ᵢ`
1. `f^Late_i(l) = fᵢ(s, l) = (Lᵢ − l)·min_j (R_j + Wᵢ)/β_{i,j}`;
2. a resource `j` is optimal in state `(s, l)` (attains the Bellman minimum
   `R_j + Wᵢ + β_{i,j} fᵢ(s+1, l+1) + β̃_{i,j} fᵢ(s+1, l) = fᵢ(s, l)`) iff `β_{i,j} > 0` and `j`
   minimizes `(R_j + Wᵢ)/β_{i,j}`, a condition that does not depend on `s` or `l`: the optimal
   resource is the same in every period, `j*(i, s, l) = j^{Late,*}_i = argmin_j (R_j + Wᵢ)/β_{i,j}`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 1, p.12.

Formalization Note: the minimum is over `{j | β_{i,j} > 0}` (`lateRatio`); on the page the other
ratios are `+∞`. -/
theorem lemma_1_late_resource (S : System) (hS : Standing S) (i : Fin S.I) (s l : ℕ)
    (hs : S.δ i ≤ s) (hl : l < S.L i) :
    orderValue S i s l = ENNReal.ofReal (((S.L i : ℝ) - l) * lateRatio S i) ∧
    ∀ j : Fin (S.J + 1),
      (ENNReal.ofReal (resCost S j + S.W i) +
          ENNReal.ofReal (S.β i j) * orderValue S i (s + 1) (l + 1) +
          ENNReal.ofReal (1 - S.β i j) * orderValue S i (s + 1) l = orderValue S i s l ↔
        (0 < S.β i j ∧ (resCost S j + S.W i) / S.β i j = lateRatio S i)) := by sorry

end CloudCostOpt
