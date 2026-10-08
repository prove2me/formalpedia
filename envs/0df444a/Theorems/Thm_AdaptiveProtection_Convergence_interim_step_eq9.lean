-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_interim_step_eq9
-- name    : AdaptiveProtection.Convergence.interim_step_eq9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:40.938989+00:00
-- url     : https://prove2.me/theorems/cc0a0c86-6a05-4296-b9fe-e8ea94a2164f
-- title:
--   Proof of Theorem 1, p. 766 — the induction step for (9): p_i(θ*) = θ*_i implies p_{i+1}(θ*) = θ*_{i+1}
-- statement:
--   Let fares satisfy $f_1 > \cdots > f_{k+1} > 0$, let the class demands be independent and nonnegative, and let $\theta^*$ satisfy the optimality condition (3):
--   $$P(A_i(\theta^*, X)) = r_{i+1} = f_{i+1}/f_1 \qquad (i = 1, \dots, k).$$
--   If $1 \le i$, $i + 1 \le k$ and $p_i(\theta^*) = \theta^*_i$, where $p_i(\theta) = \max\{\theta_j : 1 \le j \le i\}$ is the interim protection level (7), then
--   $$p_{i+1}(\theta^*) = \theta^*_{i+1}.$$
--
--   Together with the base case $p_1(\theta^*) = \theta^*_1$, this shows that the limiting protection levels are ordered, $\theta^*_1 \le \theta^*_2 \le \cdots \le \theta^*_k$, so that using the interim levels does not change the limiting policy.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 766, proof of Theorem 1, the paragraph showing (9) (right column, top)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- The induction step for (9) in the proof of Theorem 1 (p. 766): if `p_i(θ*) = θ*_i`, then
`p_{i+1}(θ*) = θ*_{i+1}`, because otherwise `A_{i+1}(θ*, X) = A_i(θ*, X)` and (3) would force
`f_{i+2} = f_{i+1}`. -/
theorem interim_step_eq9
    (k : ℕ) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i) (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (θstar : ℕ → ℝ)
    (hopt : ∀ i, 1 ≤ i → i ≤ k → (flightLaw ν).real (fillEvent θstar i) = ratio f (i + 1))
    (i : ℕ) (hi : 1 ≤ i) (hik : i + 1 ≤ k) (hIH : interim θstar i = θstar i) :
    interim θstar (i + 1) = θstar (i + 1) := by sorry

end AdaptiveProtection.Convergence
