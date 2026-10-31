-- Prove2me | Theorems.Thm_AdaDiscRL_lemma_J_1_sum_weights
-- name    : AdaDiscRL.lemma_J_1_sum_weights
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:09.674241+00:00
-- url     : https://prove2.me/theorems/977bd082-1575-4577-b115-7cf9fb375178
-- title:
--   Lemma J.1(1), first clause — $\sum_{i=1}^t\alpha^i_t=1$ (part: the other clauses are VLearning.CCE.lemma_10)
-- statement:
--   Let $\alpha_t=\frac{H+1}{H+t}$ and $\alpha^i_t=\alpha_i\prod_{j=i+1}^t(1-\alpha_j)$ (Eq. (11)). For every $t\ge1$,
--   $$
--   \sum_{i=1}^t\alpha^i_t=1 .
--   $$
--   The AdaQL estimate is the $\alpha^i_t$-weighted average of its targets, so these weights are a probability vector over the past encounters. The remaining clauses of Lemma J.1 ($\max_i\alpha^i_t\le 2H/t$, $\sum_i(\alpha^i_t)^2\le2H/t$, $\sum_i\alpha^i_t/\sqrt i\in[1/\sqrt t,2/\sqrt t]$, $\sum_{t\ge i}\alpha^i_t=1+1/H$) are the platform's open goal `VLearning.CCE.lemma_10`.
--
--   **Formalization Note** $\alpha^i_t$ is the platform definition `VLearning.CCE.lrW H t i`.
--
--   Differences from the source:
--   - generalization: horizon H ≥ 1 → every H ∈ ℕ; reason: α_1 = 1 for every H, so the identity holds for all H; H ≥ 1 is a special case
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Lemma J.1, part 1, first clause, p.63

import Mathlib
import Definitions.Def_VLearning_CCE_WeightedBandit

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Lemma J.1, part 1, first clause** (arXiv:2110.15843v3, p.63; Lemma 4.1 of Jin et al. 2018):
for the learning rates `α_t = (H+1)/(H+t)` and `α_t^i = α_i ∏_{j=i+1}^t (1 − α_j)` (Eq. (11), p.18),
`Σ_{i=1}^t α_t^i = 1` for every `t ≥ 1`. The other clauses of Lemma J.1 are the platform's
`VLearning.CCE.lemma_10`.

**Formalization Note.** `α_t^i` is the platform's `VLearning.CCE.lrW H t i`; every `H : ℕ` is
allowed. -/
theorem lemma_J_1_sum_weights (H t : ℕ) (ht : 1 ≤ t) :
    ∑ i ∈ Finset.Icc 1 t, VLearning.CCE.lrW H t i = 1 := by sorry

end AdaDiscRL
