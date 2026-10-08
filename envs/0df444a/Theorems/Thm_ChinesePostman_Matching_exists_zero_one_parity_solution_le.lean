-- Prove2me | Theorems.Thm_ChinesePostman_Matching_exists_zero_one_parity_solution_le
-- name    : ChinesePostman.Matching.exists_zero_one_parity_solution_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:40.729108+00:00
-- url     : https://prove2.me/theorems/29b4eeb0-bbad-44a9-b9fd-78942bb9afcd
-- title:
--   §3, p. 93 — reduce feasible multiplicities to zero or one
-- statement:
--   Let $x_e\in\mathbb N$ satisfy the paper's parity equations in a finite loopless multigraph, and suppose every edge cost $c_e$ is nonnegative. Then there is another parity solution $x'$ with $x'_e\in\{0,1\}$ for all edges and no greater cost:
--
--   $$
--   \forall e\in E,\quad x'_e\le1,
--   \qquad \sum_e c_ex'_e\le\sum_e c_ex_e.
--   $$
--
--   This permits the matching comparison to start with a binary parity subgraph.
--
--   **Formalization Note** The theorem applies to every feasible $x$, which is stronger than the paper's phrasing for an optimum; it follows from reducing each multiplicity by an even amount and uses only the stated nonnegative costs.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 93, §3, paragraph beginning “Consider an optimum solution”, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §3, p. 93: reducing every multiplicity modulo two preserves parity and cannot raise cost. -/
theorem exists_zero_one_parity_solution_le
    {V E : Type*} [Fintype E] [DecidableEq V]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (c : E → ℝ) (hc : ∀ e, 0 ≤ c e)
    (x : E → ℕ) (hx : IsParitySolution G x) :
    ∃ x' : E → ℕ, IsParitySolution G x' ∧
      (∀ e, x' e ≤ 1) ∧ cost c x' ≤ cost c x := by sorry
end ChinesePostman.Matching
