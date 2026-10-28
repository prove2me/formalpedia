-- Prove2me | Theorems.Thm_ConvexOn_exists_linear_upper_of_upperSemicontinuousAt
-- name    : ConvexOn.exists_linear_upper_of_upperSemicontinuousAt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T07:51:32.288575+00:00
-- url     : https://prove2.me/theorems/edf4aca8-53c9-41d8-96d3-891fef1d4ce7
-- title:
--   An extended-real function with convex hypograph is bounded above affinely in the norm
-- statement:
--   Let $E$ be a real normed space and $L : E \to \overline{\mathbb{R}}$ a function that never takes
--   the value $+\infty$. Suppose
--
--   1. the hypograph is convex: $\{(x, t) \in E \times \mathbb{R} : -L(x) \le t\}$ is a convex set;
--   2. $L$ is finite at one point: $L(x_0) = a$ for some $a \in \mathbb{R}$;
--   3. $L$ is upper semicontinuous at $x_0$.
--
--   Then $L$ grows at most affinely in the distance from $x_0$:
--
--   $$
--   \exists\, C \in \mathbb{R},\ A \ge 0 \ \text{ such that } \ L(x) \le C + A\,\|x - x_0\| \quad
--   \text{for every } x \in E .
--   $$
--
--   A concave function finite at a point and upper semicontinuous there cannot grow faster than
--   linearly away from that point, and this records the fact with an explicit affine majorant rather
--   than as a local statement. The majorant is what makes a supremum over an unbounded set
--   manageable, so this is the first step whenever a worst-case value over all of $E$ has to be
--   shown finite. Note that no continuity is assumed away from $x_0$ and the value $-\infty$ is
--   allowed everywhere.
-- source:
--   P. Mohajerin Esfahani and D. Kuhn, Data-driven distributionally robust optimization using the Wasserstein metric: performance guarantees and tractable reformulations, Mathematical Programming 171 (2018), 115-166. Carved from https://prove2.me/submissions/9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 929-996, the accepted proof of WassDDRO.Extremal.theorem_4_4. The same statement is proved inline in https://prove2.me/submissions/6e4986f7-2b7e-4a8d-97e1-f19f9c2537ac as well, the accepted proof of WassDDRO.Reduction.theorem_4_2, so two missions were each carrying their own derivation of it

import Mathlib

set_option autoImplicit false
open Filter Topology Set

theorem ConvexOn.exists_linear_upper_of_upperSemicontinuousAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E → EReal)
    (hne_top : ∀ x, L x ≠ ⊤)
    (hconvex : Convex ℝ {p : E×ℝ | -L p.1 ≤ (p.2 : EReal)})
    (x0 : E) (a : ℝ) (ha : L x0=(a : EReal))
    (husc : UpperSemicontinuousAt L x0) :
    ∃ C A : ℝ, 0 ≤ A ∧ ∀ x, L x ≤ ((C+A*‖x-x0‖ : ℝ) : EReal) := by sorry
