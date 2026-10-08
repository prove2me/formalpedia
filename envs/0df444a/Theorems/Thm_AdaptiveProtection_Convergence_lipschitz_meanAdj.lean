-- Prove2me | Theorems.Thm_AdaptiveProtection_Convergence_lipschitz_meanAdj
-- name    : AdaptiveProtection.Convergence.lipschitz_meanAdj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T23:05:29.981719+00:00
-- url     : https://prove2.me/theorems/173d788e-fdfa-4a37-b135-98385ef35fdf
-- title:
--   Proof of Theorem 1, p. 766 — |h_{i+1}(θ_{i+1}, θ*_i, …, θ*_1) − h_{i+1}(θ_{i+1}, θ_i, …, θ_1)| ≤ C Σ_{j≤i} |θ_j − θ*_j|
-- statement:
--   Let the class demands be independent with laws $\nu_1, \nu_2, \dots$, and suppose assumption A3 holds with constant $L$: for $j = 1, \dots, k$ and all real $x, y$,
--   $$|P(X_1 + \cdots + X_j < x) - P(X_1 + \cdots + X_j < y)| \le L|x - y|.$$
--   Let $1 \le i$ with $i + 1 \le k$, and let $\theta, \theta^*$ be any two vectors of protection levels. Then
--   $$\bigl|h_{i+1}(\theta_{i+1}, \theta^*_i, \dots, \theta^*_1) - h_{i+1}(\theta_{i+1}, \theta_i, \dots, \theta_1)\bigr| \le L \sum_{j=1}^{i} |\theta_j - \theta^*_j|.$$
--
--   In the proof of Theorem 1 this is applied with $\theta = \theta^n$; it controls the error made by replacing the first $i$ current levels by their (already established) limits, which is what lets the induction proceed from class $i$ to class $i+1$.
--
--   **Formalization Note** The page's generic constant $C$ is stated as A3's Lipschitz constant $L$, which is what the argument gives. The bound is deterministic in $\theta$; the page writes it for the iterate $\theta^n$.
-- source:
--   van Ryzin & McGill, Management Science 46(6), 2000, p. 766, proof of Theorem 1, first display after "Therefore, we have" (left column)

import Mathlib
import Definitions.Def_NestedSeatAlloc_ProbCond_Model
import Definitions.Def_AdaptiveProtection_Convergence_Setting

open MeasureTheory Filter Topology

namespace AdaptiveProtection.Convergence

/-- The Lipschitz bound on `h_{i+1}` in the proof of Theorem 1 (p. 766, first display after
"Therefore, we have"): replacing the first `i` levels of `θ` by those of `θ*` changes
`h_{i+1}` by at most `L ∑_{j ≤ i} |θ_j − θ*_j|`, where `L` is the Lipschitz constant of A3. -/
theorem lipschitz_meanAdj
    (k : ℕ) (f : ℕ → ℝ) (ν : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (L : ℝ)
    (hL : ∀ j, 1 ≤ j → j ≤ k → ∀ x y : ℝ,
      |(flightLaw ν).real {z | partialSum z j < x} - (flightLaw ν).real {z | partialSum z j < y}|
        ≤ L * |x - y|)
    (i : ℕ) (hi : 1 ≤ i) (hik : i + 1 ≤ k) (θ θstar : ℕ → ℝ) :
    |meanAdj f ν (fun j => if j ≤ i then θstar j else θ j) (i + 1) - meanAdj f ν θ (i + 1)|
      ≤ L * ∑ j ∈ Finset.Icc 1 i, |θ j - θstar j| := by sorry

end AdaptiveProtection.Convergence
