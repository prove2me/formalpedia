-- Prove2me | Theorems.Thm_ConvexBodyChasing_competitive_ratio_linear_lower_bound
-- name    : ConvexBodyChasing.competitive_ratio_linear_lower_bound
-- status  : Proved
-- author  : @nhc
-- created : 2026-11-13T13:39:27.977197+00:00
-- url     : https://prove2.me/theorems/0c7fdae2-d57b-4593-a290-2918bcd2d66f
-- title:
--   An explicit linear competitive-ratio lower bound in finite-dimensional $\ell_p$
-- statement:
--   Let $d\ge3$ be a natural number and let $1\le p<\infty$. Consider a randomized online algorithm $A$ for nonempty compact convex requests in $(\mathbb R^d,\|\cdot\|_p)$, starting at the origin. Randomness is represented by a probability space of seeds with measurable decisions. If $R\in\mathbb R$ satisfies the competitive guarantee against every feasible comparator path, then
--
--   $$R\ge\frac{d}{128000000}.$$
--
--   The constant is absolute and independent of $p$, the dimension, and the algorithm. This is the competitive-ratio consequence of the recursive request construction and Proposition 9, with explicit nonoptimized constants and dimension padding. It supplies the Euclidean lower bound used in the quotient-of-a-subspace reduction to an arbitrary norm.
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf, Proposition 9, p. 14, and its competitive-ratio consequence on p. 15; explicit constant and dimension padding from the accompanying local Lean formalization.

import Definitions.Def_CBCCompactChasingModel
open scoped ENNReal
open ConvexBodyChasing

theorem ConvexBodyChasing.competitive_ratio_linear_lower_bound (d : ℕ) (hd : 3 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : RandomizedOnlineAlgorithm (Space d p)) (R : ℝ)
    (hcomp : RandomizedCompetitive A 0 R) : (d : ℝ) / 128000000 ≤ R := by sorry
