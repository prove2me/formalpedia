-- Prove2me | Theorems.Thm_AllocationIndices_normal_target_index
-- name    : AllocationIndices.normal_target_index
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:03:41.341294+00:00
-- url     : https://prove2.me/theorems/ff1dd018-57f7-4995-9d20-093bbfc1abbf
-- title:
--   Example 7.6: the normal target process with known variance has index ν(x̄, n) = r(x̄, n) = Φ(x̄ (1 + 1/n)^(-1/2)) when x̄ ≥ 0
-- statement:
--   **Example 7.6.** Normal target process, known variance $1$, $T = 0$, conjugate prior $N(\bar x, 1/n)$: the predictive density is $N(\bar x, 1 + 1/n)$, $r(\bar x, n) = \Phi\big(\bar x (1 + n^{-1})^{-1/2}\big)$ (7.6), and if $\bar x \ge 0$ the state is favourable, so that $\nu(\bar x, n) = r(\bar x, n)$.
--
--   Formally: for $\bar x \ge 0$, $n > 0$ and $a \in (0, 1)$, the Gittins index of the normal target process (next observation $\bar x + \sqrt{1+1/n}\,Z$, $Z \sim N(0,1)$; target reached if it is $\ge 0$, else the state becomes $((n\bar x + x)/(n+1), n+1)$) in the state $(\bar x, n)$ equals $P(\bar x + \sqrt{1+1/n}\,Z \ge 0)$, which is $\Phi(\bar x(1 + n^{-1})^{-1/2})$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §7.3 pp. 182-183, Example 7.6 and Eq. (7.6)

import Definitions.Def_AllocationIndices_Sampling

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

/-- **Example 7.6** (p. 183), the normal target process with known variance `1`, target `0` and
conjugate prior `N(x̄, 1/n)`: if `x̄ ≥ 0` the state `(x̄, n)` is favourable, since sampling values
below the target can only lower the posterior mean, and hence
`ν(x̄, n) = r(x̄, n) = Φ(x̄ (1 + n⁻¹)^{-1/2})` (7.6), here written as the probability that
`x̄ + √(1 + 1/n) Z ≥ 0` for `Z ~ N(0, 1)`. -/
theorem normal_target_index {xb n : ℝ} (hxb : 0 ≤ xb) (hn : 0 < n) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1) :
    gittinsIndex normalTargetChain normalTargetReward a (Sum.inl (xb, n)) =
      ((gaussianReal 0 1) {z | 0 ≤ xb + Real.sqrt (1 + 1 / n) * z}).toReal := by sorry

end AllocationIndices
