-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lift_and_project_one_var
-- name    : Disjunctive.HigherDim.lift_and_project_one_var
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:38:22.578873+00:00
-- url     : https://prove2.me/theorems/548f8dcb-295a-4214-b73c-bf1f90199891
-- title:
--   Theorem 7.1 — the nonlinear 3-step lift-and-project equals split convexification
-- statement:
--   This is Theorem 7.1 of Balas's *Disjunctive Programming*, identifying the nonlinear
--   3-step construction $P_j(K)$ (multiply by $(1-x_j)$ and $x_j$, linearize, project) with the convex
--   hull of imposing $x_j \in \{0,1\}$ on $K$:
--
--   $$
--   P_j(K) = \mathrm{conv}(K \cap \{x \in \mathbb R^n : x_j \in \{0,1\}\}).
--   $$
--
--   The book proves this by rewriting $M_j(K)$'s defining system, after the substitutions $y_0 :=
--   x_j$, $z := x-y$, $z_0 := 1-y_j$, into exactly the disjunctive-set representation of Theorem
--   2.1 for the two-term disjunction $x_j = 0 \lor x_j = 1$ — so Theorem 7.1 is, in the book's own
--   words, "a special case of Theorem 2.1."
--
--   **Formalization Note.** Stated via `Pj`/`Mj` (the literal 3-step construction) on the left and
--   `SplitConvexify`/`ZeroOneSet` (the convex-hull description) on the right, matching the theorem's
--   own role as the bridge between the two.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 92, Theorem 7.1

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic

namespace Disjunctive.HigherDim

/-- Theorem 7.1 (Balas §7.1, p. 91-92): the projection `P_j(K)` of the nonlinear 3-step
construction equals `conv(K ∩ {x_j ∈ {0,1}})`. -/
theorem lift_and_project_one_var {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (j : Fin n) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
