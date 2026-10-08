-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_theorem1_case_one
-- name    : AdaptiveProtection.Convergence.theorem1_case_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:23.097984+00:00
-- url     : https://prove2.me/theorems/6f92cd02-cb7e-4911-ac77-233df49331cf
-- title:
--   Proof of Theorem 1, p. 765 — the case i = 1: θ^n_1 → θ*_1 a.s. and E|θ^n_1 − θ*_1|² ≤ Cγ_n^β
-- statement:
--   Work under the hypotheses of Theorem 1: $k \ge 1$ protection levels, fares $f_1 > \cdots > f_{k+1} > 0$, independent nonnegative class demands with continuous distributions, step sizes $\gamma_n = A/(n+B)$ with $A > 0$, $B \ge 0$, an arbitrary initial vector $\theta^1$, a vector $\theta^*$ satisfying the optimality condition (3) $P(A_i(\theta^*, X)) = r_{i+1}$ for $i = 1, \dots, k$, and the assumptions A1 (bounded support), A2 (in the windowed form described below) and A3 (Lipschitz partial-sum distributions). Then the first protection level converges almost surely,
--   $$\theta^n_1 \to \theta^*_1 \quad \text{(a.s.)},$$
--   and there are $\beta > 0$ and $C$ such that, for all $n \ge 1$, $|\theta^n_1 - \theta^*_1|^2$ is integrable and
--   $$E|\theta^n_1 - \theta^*_1|^2 \le C \gamma_n^{\beta}.$$
--
--   This is the base case of the induction on fare classes that proves Theorem 1: since $A_1(\theta, X) = \{X_1 > \theta_1\}$ depends on $\theta_1$ only, $(\theta^n_1)$ is a scalar Robbins–Monro process.
--
--   **Formalization Note** The page asserts the rate "for all $0 < \beta < 1$", citing Benveniste et al.; this is false in general (with $h_1$ of slope exactly $\delta$ at $\theta^*_1$ and $2\delta A < 1$ the error decays like $n^{-2\delta A}$), and Theorem 1 needs only some $\beta > 0$, which is what is stated. A2 is pinned as in the goal theorem: for every radius $R > 0$ there is $\delta_R > 0$ with $(t - \theta^*_i)h_i(\theta^*_1, \dots, \theta^*_{i-1}, t) \ge \delta_R |t - \theta^*_i|^2$ whenever $|t - \theta^*_i| \le R$. Lean's index $n$ is the paper's $n + 1$.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 765, proof of Theorem 1, the case of Fare Class 1 (right column, top)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- The case `i = 1` of the proof of Theorem 1 (p. 765): the first coordinate is a scalar
Robbins–Monro process, converges a.s. to `θ*_1`, and has mean-square rate `C γ_n^β` for some
`β > 0`. The page claims the rate "for all 0 < β < 1"; that is false in general (with
`h_1` of slope `δ` at `θ*_1` and `2δA < 1` the error decays like `n^{−2δA}`), and Theorem 1 uses
only the existence of one `β > 0`, which is what is stated here. -/
theorem theorem1_case_one
    (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) (hf : ∀ i, 1 ≤ i → i ≤ k → f (i + 1) < f i)
    (hfpos : 0 < f (k + 1))
    (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hnonneg : ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), 0 ≤ t)
    (hcont : ∀ i, 1 ≤ i → i ≤ k + 1 → NullSingletonClass (ν i))
    (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (θ₁ θstar : ℕ → ℝ)
    (hopt : ∀ i, 1 ≤ i → i ≤ k → (flightLaw ν).real (fillEvent θstar i) = ratio f (i + 1))
    (hA1 : ∃ Cb : ℝ, ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ᵐ t ∂(ν i), t < Cb)
    (hA2 : ∀ R > 0, ∃ δ > 0, ∀ i, 1 ≤ i → i ≤ k → ∀ t : ℝ, |t - θstar i| ≤ R →
      δ * (t - θstar i) ^ 2 ≤ (t - θstar i) * meanAdj f ν (Function.update θstar i t) i)
    (hA3 : ∃ L : ℝ, ∀ i, 1 ≤ i → i ≤ k → ∀ x y : ℝ,
      |(flightLaw ν).real {z | partialSum z i < x} - (flightLaw ν).real {z | partialSum z i < y}|
        ≤ L * |x - y|) :
    (∀ᵐ ω ∂(pathLaw ν),
        Tendsto (fun n => iterate f k (stepSize A B) θ₁ ω n 1) atTop (𝓝 (θstar 1))) ∧
    (∃ β > 0, ∃ C : ℝ, ∀ n : ℕ,
        Integrable (fun ω => (iterate f k (stepSize A B) θ₁ ω n 1 - θstar 1) ^ 2) (pathLaw ν) ∧
        ∫ ω, (iterate f k (stepSize A B) θ₁ ω n 1 - θstar 1) ^ 2 ∂(pathLaw ν)
          ≤ C * stepSize A B (n + 1) ^ β) := by sorry

end AdaptiveProtection.Convergence
