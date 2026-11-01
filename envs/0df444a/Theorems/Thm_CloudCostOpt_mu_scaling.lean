-- Prove2me | Theorems.Thm_CloudCostOpt_mu_scaling
-- name    : CloudCostOpt.mu_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:09:09.102326+00:00
-- url     : https://prove2.me/theorems/fa8d0b3b-7167-4960-a2e1-d1a8fffd6060
-- title:
--   p.18 — $\mu_j$ scales linearly with the demand rates
-- statement:
--   If the vector of demand rates $(\lambda_1,\dots,\lambda_I)$ is scaled by $\theta\ge0$, then for every real resource type $j$
--
--   $$
--   \mu_j(\theta)=\theta\,\mu_j(1),
--   $$
--
--   where $\mu_j(\theta)$ is computed from (6)–(7) with the rates $\theta\lambda$ and the same selection $j^*$ (the selection does not depend on the demand rates).
--
--   Together with (14), this gives the $\sqrt\theta$ scaling of the bound on the optimality gap in Corollary 6.
--
--   Differences from the source:
--   - reading: I ≥ 1 order types, Lᵢ ≥ 1 steps and Poisson rates λᵢ > 0, implicit in the model of pp.3–4 → explicit hypotheses 0 < I, 1 ≤ Lᵢ (Standing) and λᵢ > 0; reason: an order has at least one step (the state space is 0 ≤ l ≤ Lᵢ − 1) and a Poisson process has a positive rate
--   - reading: sign of the waiting cost Wᵢ not stated → Wᵢ > 0 (Standing); reason: with Wᵢ = 0 an order can idle forever at no cost, so LB = 0 and (10) fails; the numerical study draws Wᵢ > 0
--   - generalization: j*(i, s, l) and j^{Late,*}_i are "the" argmin → any selection of minimizers (Selection); reason: the paper leaves ties unspecified; its own choice is one selection, so the statement specializes to it
--   - encoding: µ_j as a real number → µ_j computed in [0, ∞], and the identity stated there; reason: Lean convention for a sum of nonnegative terms; µ_j is finite by Lemma 3
--   - encoding: θ ≥ 0 real → θ : ℝ≥0; reason: Lean convention; same values
-- source:
--   Qu, Dawande, Janakiraman, Cloud Cost Optimization: Model, Bounds, and Asymptotics, SSRN 4166245, §5, p.18

import Mathlib
import Definitions.Def_CloudCostOpt_mu
import Definitions.Def_CloudCostOpt_Standing

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CloudCostOpt

/-- **`μ_j` scales with demand** (p.18): if the arrival rates `(λ₁, …, λ_I)` are scaled by `θ ≥ 0`,
then `μ_j(θ) = θ · μ_j(1)` for every `j`; the same selection `j*` serves every `θ`, because `j*`
does not depend on the arrival rates.

Qu, Dawande, Janakiraman, *Cloud Cost Optimization: Model, Bounds, and Asymptotics*, SSRN 4166245, §5, p.18 ("It is also easy to verify using the analysis in Section 3 (see definition (7))
that `μ_j` also scales proportionally to `θ`"). -/
theorem mu_scaling (S : System) (hS : Standing S) (sel : Selection S)
    (lam : Fin S.I → ℝ≥0) (hlam : ∀ i, 0 < lam i) (θ : ℝ≥0) (j : Fin S.J) :
    mu S sel (θ • lam) j = (θ : ℝ≥0∞) * mu S sel lam j := by sorry

end CloudCostOpt
