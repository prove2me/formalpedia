-- Prove2me | Theorems.Thm_AnalyticGeometry_evalR_ker_principal
-- name    : AnalyticGeometry.evalR_ker_principal
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-19T13:58:39.493801+00:00
-- url     : https://prove2.me/theorems/082dbd9d-c9e5-4260-8706-2d3aed28c8c4
-- title:
--   The kernel of evaluation at a real $x \in (0, r]$ is principal
-- statement:
--   Let $0 < x \le r < 1$. There is an element $f \in \mathbb{Z}((T))_{>r}$ generating the
--   kernel of evaluation at $x$: for every $g \in \mathbb{Z}((T))_{>r}$,
--   $$g(x) = 0 \iff g = f h \text{ for some } h \in \mathbb{Z}((T))_{>r}.$$
--
--   This is the principality assertion of case (1) of Theorem 7.1 of the source for real $x$. The
--   generator is built as $f = g_\ast h_\ast$, where $g_\ast \in 1 + T^n\mathbb{R}[T]$ has $x$ as its
--   only zero in the punctured closed disc and $h_\ast \in 1 + T^n\mathbb{R}[[T]]$ has all coefficients
--   bounded by $1/2$ and is chosen so that the product has integer coefficients; choosing $n$ with
--   $r^n < 2(1-r)$ makes $h_\ast$ invertible on $\{0 < |y| \le r\}$, so $f$ acquires no further zeros
--   there. Divisibility then follows because $f \in 1 + T\mathbb{Z}[[T]]$ is invertible in
--   $\mathbb{Z}[[T]]$, and the quotient $g/f$ remains holomorphic on a disc of radius $> r$.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

namespace AnalyticGeometry

/-- The kernel of evaluation at a real point `0 < x ≤ r` is principal. -/
theorem evalR_ker_principal (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hx0 : 0 < x) (hxr : x ≤ r) :
    ∃ f ∈ zLaurentGT r, ∀ g ∈ zLaurentGT r,
      (evalR x g = 0 ↔ ∃ h ∈ zLaurentGT r, g = f * h) := by
  sorry

end AnalyticGeometry
