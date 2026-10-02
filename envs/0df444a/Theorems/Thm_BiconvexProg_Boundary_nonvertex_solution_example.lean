-- Prove2me | Theorems.Thm_BiconvexProg_Boundary_nonvertex_solution_example
-- name    : BiconvexProg.Boundary.nonvertex_solution_example
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:49:43.364981+00:00
-- url     : https://prove2.me/theorems/4fb79572-fa95-4fbc-bbb1-4794711c22ac
-- title:
--   Example, p. 274: a jointly constrained bilinear program whose solution is not an extreme point (corrected to $(7/6, 1/2)$)
-- statement:
--   Consider the jointly constrained bilinear program
--
--   $$\min_{(x,y)} \; -x + xy - y \quad \text{subject to} \quad -6x + 8y \le 3,\quad 3x - y \le 3,\quad 0 \le x \le 5,\quad 0 \le y \le 5.$$
--
--   Let $T \subseteq \mathbb{R}^2$ be its feasible region (a quadrilateral with vertices $(0,0)$, $(1,0)$, $(3/2, 3/2)$, $(0, 3/8)$). Then
--
--   1. $(7/6, 1/2) \in T$ and it is a global minimizer of $-x + xy - y$ over $T$;
--   2. $(7/6, 1/2)$ is not an extreme point of $T$;
--   3. no extreme point of $T$ is a minimizer.
--
--   The example shows that the extreme-point property of the traditional (separably constrained) bilinear program is lost once the constraints couple $x$ and $y$; Theorem 1 replaces "extreme point" by "boundary point".
--
--   **Formalization Note** The paper prints the solution as $(7/16, 1/2)$, which is a misprint: at $(7/16, 1/2)$ the objective is $-23/32$, while the feasible vertex $(1,0)$ gives $-1$. On the edge $3x - y = 3$ the objective equals $3x^2 - 7x + 3$, minimized at $x = 7/6$ with value $-13/12$, which is the global minimum over $T$. The statement uses the corrected point $(7/6, 1/2)$, which lies on that edge and not at a vertex.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, example of a jointly constrained bilinear program (printed solution (7/16, 1/2) corrected to (7/6, 1/2))

import Mathlib

namespace BiconvexProg.Boundary

/-- Jointly constrained example (Al-Khayyal–Falk 1983, p. 274), with the printed solution
`(7/16, 1/2)` corrected to `(7/6, 1/2)`: over the polygon
`T = {(x, y) : −6x + 8y ≤ 3, 3x − y ≤ 3, 0 ≤ x ≤ 5, 0 ≤ y ≤ 5}`, the point `(7/6, 1/2)` is a
feasible global minimizer of `−x + xy − y` that is not an extreme point of `T`, and no extreme
point of `T` is a minimizer. -/
theorem nonvertex_solution_example :
    let T : Set (ℝ × ℝ) := {z | -6 * z.1 + 8 * z.2 ≤ 3 ∧ 3 * z.1 - z.2 ≤ 3 ∧
      0 ≤ z.1 ∧ z.1 ≤ 5 ∧ 0 ≤ z.2 ∧ z.2 ≤ 5}
    let f : ℝ × ℝ → ℝ := fun z => -z.1 + z.1 * z.2 - z.2
    ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∈ T ∧ IsMinOn f T ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∧
      ((7 / 6 : ℝ), (1 / 2 : ℝ)) ∉ Set.extremePoints ℝ T ∧
      ∀ z ∈ Set.extremePoints ℝ T, ¬ IsMinOn f T z := by sorry

end BiconvexProg.Boundary
