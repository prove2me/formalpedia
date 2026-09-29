-- Prove2me | Theorems.Thm_AnalyticGeometry_evalR_surjective
-- name    : AnalyticGeometry.evalR_surjective
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T13:54:35.576527+00:00
-- url     : https://prove2.me/theorems/f8a2dd48-dfb9-42d7-8092-26d3af3bf617
-- title:
--   Evaluation at a real point $0 < x \le r$ is surjective onto $\mathbb{R}$
-- statement:
--   Let $0 < x \le r < 1$. Every real number $y$ is a value of an overconvergent integral
--   Laurent series at $x$:
--   $$\forall y \in \mathbb{R},\ \exists f \in \mathbb{Z}((T))_{>r},\quad \sum_{n} f_n x^{\,n} = y,$$
--   the sum being absolutely convergent.
--
--   This is the surjectivity step in case (1) of Theorem 7.1 of the source. The argument there is a
--   greedy expansion: fixing an integer $N$ with $x \ge 1/N$, every $y \ge 0$ is represented by a series
--   in $x$ with digits in $\{0, \dots, N-1\}$, obtained by repeatedly subtracting the largest multiple
--   $a_n x^{\,n} \le y$; when $x = 1/N$ this is the base-$N$ expansion. Series with bounded integer
--   coefficients are overconvergent for any radius $< 1$, so the representing series lies in
--   $\mathbb{Z}((T))_{>r}$.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

namespace AnalyticGeometry

/-- Surjectivity of evaluation at a real point `0 < x ≤ r`. -/
theorem evalR_surjective (r x : ℝ) (hr1 : r < 1) (hx0 : 0 < x) (hxr : x ≤ r) (y : ℝ) :
    ∃ f ∈ zLaurentGT r,
      Summable (fun n : ℤ => (f.coeff n : ℝ) * x ^ n) ∧ evalR x f = y := by
  sorry

end AnalyticGeometry
