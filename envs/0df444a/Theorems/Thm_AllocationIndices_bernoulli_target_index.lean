-- Prove2me | Theorems.Thm_AllocationIndices_bernoulli_target_index
-- name    : AllocationIndices.bernoulli_target_index
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T03:03:16.005972+00:00
-- url     : https://prove2.me/theorems/a5f7cb9f-46e7-4670-9830-321ddb0ad8dc
-- title:
--   Example 7.5: the Bernoulli target process with a beta prior has index ν(α, β) = r(α, β) = α/(α + β)
-- statement:
--   **Example 7.5.** Bernoulli target process, $T = 1$, beta prior with parameters $\alpha, \beta > 0$: $r(\alpha, \beta) = \alpha/(\alpha + \beta)$, the sequence of states starting from $(\alpha, \beta)$ is $(\alpha, \beta), (\alpha, \beta + 1), \dots, C$, every state is favourable since $\alpha/(\alpha+\beta) \ge \alpha/(\alpha+\beta+n)$, and hence $\nu(\alpha, \beta) = r(\alpha, \beta) = \alpha/(\alpha + \beta)$.
--
--   Formally: for $\alpha, \beta > 0$ and $a \in (0, 1)$, the Gittins index of the Bernoulli target process (from $(\alpha, \beta)$ the target is reached with probability $\alpha/(\alpha+\beta)$, otherwise the state becomes $(\alpha, \beta+1)$; reward $\alpha/(\alpha+\beta)$ in $(\alpha, \beta)$ and $0$ in $C$) in the state $(\alpha, \beta)$ equals $\alpha/(\alpha + \beta)$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.3 p. 182, Example 7.5

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Example 7.5** (p. 182), the Bernoulli target process with `T = 1` and a beta prior with
parameters `α, β > 0`: every state `(α, β)` is favourable, since `α/(α + β) ≥ α/(α + β + n)`,
and hence `ν(α, β) = r(α, β) = α/(α + β)`. -/
theorem bernoulli_target_index {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    gittinsIndex bernoulliTargetChain bernoulliTargetReward a (Sum.inl (α, β)) =
      α / (α + β) := by sorry

end AllocationIndices
