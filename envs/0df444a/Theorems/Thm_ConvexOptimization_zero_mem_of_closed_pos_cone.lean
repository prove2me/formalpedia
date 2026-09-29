-- Prove2me | Theorems.Thm_ConvexOptimization_zero_mem_of_closed_pos_cone
-- name    : ConvexOptimization.zero_mem_of_closed_pos_cone
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-08-15T04:45:59.56696+00:00
-- url     : https://prove2.me/theorems/9b72d983-ead2-4efb-94ff-b1688308b063
-- title:
--   A nonempty closed cone contains the origin
-- statement:
--   Boyd and Vandenberghe define a cone by nonnegative homogeneity: $C$ is a cone when $\theta x \in C$ for every $x \in C$ and every $\theta \ge 0$, so that $0 \in C$ holds by definition (take $\theta = 0$).
--
--   It is often more convenient to hypothesise only *positive* homogeneity, i.e. $t x \in K$ for $t > 0$, since that is what one verifies in practice. This statement records that the two formulations agree for a nonempty closed cone: if $K \subseteq \mathbb{R}^d$ is nonempty, closed, and satisfies
--
--   $$t > 0,\quad y \in K \quad \Longrightarrow \quad t y \in K,$$
--
--   then $0 \in K$.
--
--   The origin is recovered as a limit rather than by substitution: picking any $y \in K$, the points $y / k$ lie in $K$ for every $k \ge 1$ and converge to $0$, which therefore belongs to $K$ by closedness. Closedness cannot be dropped — an open half-line $\{t y : t > 0\}$ is positively homogeneous and nonempty but misses the origin.
--
--   This is the bridge lemma needed whenever a cone is presented by positive homogeneity but an argument requires the apex, for instance when checking that a perturbation set built over a conic constraint is convex.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 25, §2.1.5 (cones and conic combinations)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.zero_mem_of_closed_pos_cone {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKclosed : IsClosed K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K) (hne : K.Nonempty) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ K := by sorry
