-- Prove2me | Theorems.Thm_BiasVarianceMinimax_uniform_floor
-- name    : BiasVarianceMinimax.uniform_floor
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:20.415408+00:00
-- url     : https://prove2.me/theorems/fbf016c4-277a-4d8c-95bd-5424ea963309
-- title:
--   p.55 — the uniform floor of the scaled quadratic
-- statement:
--   As $n\to\infty$, for large $n$ the quadratic $\xi_{11}a^2+2\xi_{12}a+\xi_{22}$ has a minimum $m_n$ over $a\in\mathbb R$, and
--
--   $$n^{q_1/(q_1+q_2)}\,m_n\to\frac{q_1}{q_1+q_2}.$$
--
--   Moreover, for every array with $\sum_j w_{j,n}\to 1$,
--
--   $$\liminf_{n\to\infty}\ n^{q_1/(q_1+q_2)}\sum_{j=1}^n (j+n_0)^{2\alpha q_2}w_{j,n}^2\ \ge\ \frac{q_1}{q_1+q_2}.$$
--
--   This is the lower bound that no choice of weights can beat.
--
--   Differences from the source:
--   - generalization: Appendix C assumes n₀ = 0 → the statement holds for every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
--   - generalization: the floor for the quadratic on ã, and sums equal to 1 → also for an arbitrary array with sums 1 + o(1); reason: the first clause is the page's; the second is what pp.57–58 use it for, and it implies the case of sums equal to 1
--   - encoding: min over ã, liminf → `IsLeast` for large n; the liminf bound written with ε; reason: the ε form means the same when the sequence is unbounded
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, p.55; pp.57–58

import Mathlib
import Definitions.Def_BiasVarianceMinimax_IsOptimal
import Definitions.Def_BiasVarianceMinimax_weightStar

open Filter Topology

namespace BiasVarianceMinimax

/-- **The uniform floor.** Lam, Zhang & Zhang, arXiv:1902.04673v1, p.55:
`min_ã n^(q₁/(q₁+q₂)) Z̄ₙ∗(ã)² = (q₁/(q₁+q₂))(1 + o(1))`.

First clause: the minimum over `a ∈ ℝ` of `ξ₁₁ a² + 2 ξ₁₂ a + ξ₂₂` exists for large `n`, and its
scaled value tends to `q₁/(q₁+q₂)`. Second clause: for an arbitrary array with `∑ⱼ wⱼ,ₙ → 1`,
`liminf n^(q₁/(q₁+q₂)) ∑ⱼ (j + n₀)^(2αq₂) wⱼ,ₙ² ≥ q₁/(q₁+q₂)`.

**Formalization Note.** The second clause is what the floor means for a general array, whose sum is
`1 + o(1)` (pp.57–58). The `liminf` is written with `ε`, so that it means the same when the sequence
is unbounded. With the shift `n₀`. -/
theorem uniform_floor (q₁ q₂ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (n₀ : ℕ) :
    (∃ m : ℕ → ℝ, (∀ᶠ n in atTop, IsLeast (Set.range (quadForm q₁ q₂ n₀ n)) (m n)) ∧
      Tendsto (fun n : ℕ => (n : ℝ) ^ (q₁ / (q₁ + q₂)) * m n) atTop (𝓝 (q₁ / (q₁ + q₂)))) ∧
    ∀ W : TriangularArray, Tendsto (fun n : ℕ => ∑ j, W n j) atTop (𝓝 1) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        q₁ / (q₁ + q₂) - ε ≤ (n : ℝ) ^ (q₁ / (q₁ + q₂)) * sigmaSum q₁ q₂ n₀ n (W n) := by sorry

end BiasVarianceMinimax
