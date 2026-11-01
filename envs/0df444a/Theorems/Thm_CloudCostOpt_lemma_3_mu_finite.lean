-- Prove2me | Theorems.Thm_CloudCostOpt_lemma_3_mu_finite
-- name    : CloudCostOpt.lemma_3_mu_finite
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:09:09.292905+00:00
-- url     : https://prove2.me/theorems/30ce722c-6af4-45d7-b84a-d751fee075dd
-- title:
--   Lemma 3 — $\mu_j<\infty$
-- statement:
--   For every real resource type $1\le j\le J$, the mean usage
--
--   $$
--   \mu_j=\sum_{i=1}^{I}\sum_{(s,l):\,0\le l\le\min(L_i-1,s),\ j^*(i,s,l)=j}\lambda^x_i(s,l)
--   $$
--
--   of (7) is finite: $\mu_j<\infty$.
--
--   The finiteness of $\mu_j$ is what makes $\pi^*$, whose reservation level is $\mu_j+z_j\sqrt{\mu_j}$, well defined.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - encoding: µ_j < ∞ for a sum of nonnegative terms → µ_j computed in [0, ∞], stated < ⊤; reason: Lean convention; same meaning
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, Lemma 3, p.15

import Mathlib
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **Lemma 3** (p.15): for every `1 ≤ j ≤ J`, `μ_j < ∞`.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, Lemma 3, p.15. -/
theorem lemma_3_mu_finite (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (j : Fin S.J) :
    mu S sel lam j < ⊤ := by sorry

end CloudCostOpt
