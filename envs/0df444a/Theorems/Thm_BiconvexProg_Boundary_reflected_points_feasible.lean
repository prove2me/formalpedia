-- Prove2me | Theorems.Thm_BiconvexProg_Boundary_reflected_points_feasible
-- name    : BiconvexProg.Boundary.reflected_points_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T17:48:56.005987+00:00
-- url     : https://prove2.me/theorems/14f78664-0d6b-495e-9280-f174943a3d92
-- title:
--   Proof of Theorem 1: the reflected point $(s,t) = 2(\bar x,\bar y) - (x^*,y^*)$, and $(x^*,t)$, $(s,y^*)$, are feasible
-- statement:
--   Let $S \subseteq \mathbb{R}^p \times \mathbb{R}^q$ be compact, let $(\bar x, \bar y)$ be a point of the interior of $S$, and let $(x^*, y^*) \in \partial S$ be a boundary point of $S$ nearest to $(\bar x, \bar y)$ in the Euclidean distance $d$, so that $d^* = d\big((\bar x, \bar y), (x^*, y^*)\big) \le d\big((\bar x, \bar y), w\big)$ for every $w \in \partial S$. Put
--
--   $$(s, t) = 2(\bar x, \bar y) - (x^*, y^*),$$
--
--   so that $(\bar x, \bar y)$ is the midpoint of the segment joining $(s,t)$ and $(x^*, y^*)$. Then
--
--   1. every point $w$ with $d\big((\bar x, \bar y), w\big) \le d^*$ lies in $S$;
--   2. $(s, t) \in S$;
--   3. $(x^*, t) \in S$;
--   4. $(s, y^*) \in S$.
--
--   This is the construction step of the proof of Theorem 1. The paper states only that $(s,t)$ is feasible; the next display of the proof also evaluates $\varphi$ at $(x^*, t)$ and $(s, y^*)$ and uses concavity along segments joining these points, which is why the lemma records the whole closed Euclidean ball of radius $d^*$ and the two mixed points.
--
--   **Formalization Note** Items 3 and 4 and the ball in item 1 are used silently by the paper's proof and are stated here explicitly. All four points lie at Euclidean distance exactly $d^*$ from $(\bar x, \bar y)$, or less.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, Proof of Theorem 1, last paragraph ('Let (s, t) = 2(x̄, ȳ) − (x*, y*) … Note that (s, t) is feasible.')

import Mathlib
import Definitions.Def_BiconvexProg_Boundary_eucDist

namespace BiconvexProg.Boundary

/-- Proof of Theorem 1 (Al-Khayyal–Falk 1983, p. 274): if `z̄ = (x̄, ȳ)` is an interior point of a
compact set `S ⊆ ℝᵖ × ℝ^q` and `z* = (x*, y*)` is a point of `∂S` nearest to `z̄` in Euclidean
distance, then every point within Euclidean distance `d* = eucDist z̄ z*` of `z̄` lies in `S`; in
particular, with `(s, t) = 2(x̄, ȳ) − (x*, y*)`, the points `(s, t)`, `(x*, t)` and `(s, y*)` are
feasible. -/
theorem reflected_points_feasible {p q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))) (hS : IsCompact S)
    (zbar zstar : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q))
    (hzbar : zbar ∈ interior S) (hzstar : zstar ∈ frontier S)
    (hnear : ∀ w ∈ frontier S, eucDist zbar zstar ≤ eucDist zbar w) :
    (∀ w, eucDist zbar w ≤ eucDist zbar zstar → w ∈ S) ∧
    ((2 : ℝ) • zbar.1 - zstar.1, (2 : ℝ) • zbar.2 - zstar.2) ∈ S ∧
    (zstar.1, (2 : ℝ) • zbar.2 - zstar.2) ∈ S ∧
    ((2 : ℝ) • zbar.1 - zstar.1, zstar.2) ∈ S := by sorry

end BiconvexProg.Boundary
