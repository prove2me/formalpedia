-- Prove2me | Theorems.Thm_BiconvexProg_Boundary_bilinear_local_solutions
-- name    : BiconvexProg.Boundary.bilinear_local_solutions
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T17:50:06.54068+00:00
-- url     : https://prove2.me/theorems/d60937e2-9880-43da-9f30-ba575b669181
-- title:
--   Example, p. 274: $\min\{xy : -1 \le x \le 2,\ -2 \le y \le 3\}$ has local solutions at $(-1,3)$ and $(2,-2)$
-- statement:
--   Let $B = \{(x, y) \in \mathbb{R}^2 : -1 \le x \le 2,\ -2 \le y \le 3\}$ and $f(x, y) = xy$. Then
--
--   1. $(-1, 3)$ is a local minimizer of $f$ on $B$;
--   2. $(2, -2)$ is a local minimizer of $f$ on $B$;
--   3. $(-1, 3)$ is not a global minimizer of $f$ on $B$.
--
--   The example illustrates that a bilinear program, although each product term $x_i y_i$ is quasiconvex, can have proper local solutions: local minima that are not global ($f(-1,3) = -3 > -4 = f(2,-2)$).
--
--   **Formalization Note** "Local solution" is read as local minimality relative to $B$. Item 3 records the word "proper" from the surrounding sentence ("proper local solutions are possible"), which the example is given to illustrate.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274, 'Immediate extensions', example min{xy : −1 ≤ x ≤ 2, −2 ≤ y ≤ 3}

import Mathlib

namespace BiconvexProg.Boundary

/-- Local-solution example (Al-Khayyal–Falk 1983, p. 274): the problem
`min {xy : −1 ≤ x ≤ 2, −2 ≤ y ≤ 3}` has local solutions at `(−1, 3)` and `(2, −2)`, and the
first is a proper local solution (not a global one). -/
theorem bilinear_local_solutions :
    let B : Set (ℝ × ℝ) := {z | -1 ≤ z.1 ∧ z.1 ≤ 2 ∧ -2 ≤ z.2 ∧ z.2 ≤ 3}
    let f : ℝ × ℝ → ℝ := fun z => z.1 * z.2
    IsLocalMinOn f B ((-1 : ℝ), (3 : ℝ)) ∧ IsLocalMinOn f B ((2 : ℝ), (-2 : ℝ)) ∧
      ¬ IsMinOn f B ((-1 : ℝ), (3 : ℝ)) := by sorry

end BiconvexProg.Boundary
