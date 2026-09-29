-- Prove2me | Theorems.Thm_AnalyticGeometry_zLaurentGT_isSubring
-- name    : AnalyticGeometry.zLaurentGT_isSubring
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T13:34:20.365343+00:00
-- url     : https://prove2.me/theorems/c2b062ff-f3df-4ac7-a18d-2af99c5f5418
-- title:
--   $\mathbb{Z}((T))_{>r}$ is a subring of $\mathbb{Z}((T))$
-- statement:
--   For every real $r$ with $0 < r < 1$, the overconvergent set
--   $$\mathbb{Z}((T))_{>r} = \Big\{ \sum_{n \gg -\infty} a_n T^n \;\Big|\; \exists\, s > r,\ |a_n| s^{\,n} \to 0 \Big\}$$
--   is a subring of $\mathbb{Z}((T))$: it contains $0$ and $1$ and is closed under addition, negation
--   and the Cauchy product.
--
--   This is the content hidden in the phrase "the ring $\mathbb{Z}((T))_{>r}$" in the statement of
--   Theorem 7.1 of the source. Closure under multiplication is the substantive part: if $f$ decays at
--   radius $s$ and $g$ at radius $s'$, one has to produce a single radius, strictly larger than $r$, at
--   which the Cauchy product decays, which uses that decay at a radius implies absolute summability at
--   every strictly smaller radius.
-- source:
--   Peter Scholze (all results joint with Dustin Clausen), Lectures on Analytic Geometry, Lecture VII, pp. 42-44, Theorem 7.1 (attributed there to D. Harbater, Convergent arithmetic power series, Amer. J. Math. 106 (1984), 801-846). https://www.math.uni-bonn.de/people/scholze/Analytic.pdf

import Mathlib
import Definitions.Def_AnalyticGeometry_ZLaurentGT

namespace AnalyticGeometry

/-- `ℤ((T))_{>r}` is a subring of `ℤ((T))`. -/
theorem zLaurentGT_isSubring (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ R : Subring (LaurentSeries ℤ), (R : Set (LaurentSeries ℤ)) = zLaurentGT r := by
  sorry

end AnalyticGeometry
