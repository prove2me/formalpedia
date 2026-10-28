-- Prove2me | Theorems.Thm_ERealFn_jensen_finite_sum
-- name    : ERealFn.jensen_finite_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:22:50.32699+00:00
-- url     : https://prove2.me/theorems/afe0f6ea-c1e6-4edd-bd79-a189dda3d7dd
-- title:
--   Jensen's inequality for a finite convex combination, through the epigraph, for an $\overline{\mathbb{R}}$-valued function
-- statement:
--   Let $H$ be a real inner product space and let $f : H \to \overline{\mathbb{R}}$ be a function whose epigraph
--
--   $$
--   \{(x,t) \in H \times \mathbb{R} \;:\; f(x) \le t\}
--   $$
--
--   is convex. Let $s$ be a finite index set, let $w_i \ge 0$ for $i \in s$ with $\sum_{i \in s} w_i = 1$, and let $y_i \in H$ with $f(y_i) = a_i \in \mathbb{R}$ for every $i \in s$. Then
--
--   $$
--   f\Big(\sum_{i \in s} w_i\, y_i\Big) \;\le\; \sum_{i \in s} w_i\, a_i .
--   $$
--
--   Two things make this the form a proof actually needs. First, convexity is assumed *of the
--   epigraph* rather than through an inequality on $f$: for an $\overline{\mathbb{R}}$-valued
--   function that is the usable definition, since the pointwise inequality
--   $f(\lambda x + (1-\lambda)y) \le \lambda f(x) + (1-\lambda) f(y)$ has to contend with
--   $\infty - \infty$. Second, the values are given as *real numbers* $a_i$, so the right-hand side
--   is a real and the conclusion can be chained with ordinary arithmetic -- which is what a
--   convergence-rate estimate does with it, taking $w_i = (i+1) \big/ \binom{n+1}{2}$ and
--   $y_i$ the iterates, to bound the objective at the weighted average by the weighted average of
--   the objective values.
--
--   **Formalization Note** The proof is one application of `Convex.sum_mem` to the points
--   $(y_i, a_i)$ of the epigraph, followed by `simp` to push the sum through the two projections.
--   Finiteness of $f$ at each $y_i$ enters only through the hypothesis $f(y_i) = a_i$.
-- source:
--   The Jensen step of the weighted ergodic rate in Davis & Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017) 829-858, DOI 10.1007/s11228-017-0421-z, proof of Theorem 3.2, p. 840; stated here for a general finite index set and general weights.

import Mathlib

namespace ERealFn

/-- Jensen's inequality for a finite convex combination, for an `EReal`-valued function given
through the convexity of its epigraph, at points where the function is finite. -/
theorem jensen_finite_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hconv : Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)})
    (s : Finset ℕ) (w : ℕ → ℝ) (y : ℕ → H) (a : ℕ → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, f (y i) = a i) :
    f (∑ i ∈ s, w i • y i) ≤ ((∑ i ∈ s, w i * a i : ℝ) : EReal) := by sorry

end ERealFn
