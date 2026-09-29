-- Prove2me | Theorems.Thm_AnalyticGeometry_isUnit_of_no_zeros
-- name    : AnalyticGeometry.isUnit_of_no_zeros
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T15:03:33.21558+00:00
-- url     : https://prove2.me/theorems/3fb8eec0-b71e-4efa-b517-c897a5a5f93d
-- title:
--   A zero-free element of $1 + T\mathbb{Z}[[T]]$ is a unit of $\mathbb{Z}((T))_{>r}$
-- statement:
--   Let $0 < r < 1$ and let $f \in \mathbb{Z}((T))_{>r}$ with $f \in 1 + T\mathbb{Z}[[T]]$,
--   i.e. with no terms in negative degrees and constant term $1$. If $f$ has no zero in the punctured
--   closed disc $\{\, y \in \mathbb{C} : 0 < |y| \le r \,\}$, then $f$ is a unit of
--   $\mathbb{Z}((T))_{>r}$.
--
--   This is the concluding step of the proof of Theorem 7.1 in the source: after dividing out the
--   generators of all the maximal ideals containing it, the remaining element has constant term $1$, so
--   "$f^{-1} \in 1 + T\mathbb{Z}[[T]]$, and it still has convergence radius $> r$ as $f$ has no zeroes
--   on the closed disc of radius $r$. Thus, $f$ is invertible." The formal inverse is integral for
--   algebraic reasons; the substance is that it is again overconvergent.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

namespace AnalyticGeometry

/-- An element of `1 + T ℤ[[T]]` lying in `ℤ((T))_{>r}` and having no zero on the punctured
closed disc of radius `r` is a unit of `ℤ((T))_{>r}`. -/
theorem isUnit_of_no_zeros (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (f : LaurentSeries ℤ)
    (hf : f ∈ zLaurentGT r) (hf0 : f.coeff 0 = 1) (hfneg : ∀ n : ℤ, n < 0 → f.coeff n = 0)
    (hzero : ∀ y : ℂ, 0 < ‖y‖ → ‖y‖ ≤ r → evalC y f ≠ 0) :
    ∃ g ∈ zLaurentGT r, f * g = 1 := by
  sorry

end AnalyticGeometry
