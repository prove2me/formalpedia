-- Prove2me | Theorems.Thm_Disjunctive_LiftProject_fractionality_intermediate_points_v2
-- name    : Disjunctive.LiftProject.fractionality_intermediate_points_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:27.563576+00:00
-- url     : https://prove2.me/theorems/6cc2b91a-b259-4a03-a3c2-703913c0f56a
-- title:
--   Theorem 6.1 — fractionality of intermediate points in sequential convexification
-- statement:
--   This is Theorem 6.1 of Balas's *Disjunctive Programming*. Let $P = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_k \le 1$ ($k \in N'$), let $1, j \in N'$, $P_1 = \mathrm{conv}(P \cap \{x_1 \in \{0,1\}\})$ and $P_{1j} = \mathrm{conv}(P_1 \cap \{x_j \in \{0,1\}\})$. If $\alpha x \ge \beta$ is valid for $P_{1j}$ and $x^*$ is an extreme point of $P_1 \cap \{x : \alpha x \ge \beta\}$, then
--
--   $$0 < x^*_1 < 1 \implies 0 < x^*_j < 1.$$
--
--   **Formalization Note.** The retired version allowed an arbitrary polyhedron and arbitrary coordinates; for $P = [0,1] \times \{2\}$ the second step is empty and the conclusion fails at $x^*_j = 2$. Throughout Chapter 6 the LP relaxation is $P = \{x : \tilde A x \ge \tilde b\}$ with the inequalities $x \ge 0$ and $x_j \le 1$ ($j \in N'$) included in $\tilde A x \ge \tilde b$. This is now the explicit hypothesis `HasBoundRows Atil btil N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $P$. Both coordinates are 0-1 variables ($\in N'$), as in the book.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §6.2, p. 81, Theorem 6.1

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows

namespace Disjunctive.LiftProject

/-- Theorem 6.1 (Balas, *Disjunctive Programming*, Springer 2018, §6.2, p. 81): let
`P = {x : Ãx ≥ b̃}` be the LP relaxation of a mixed 0-1 program with 0-1 index set `N'`, the
bound rows `x ≥ 0` and `x_j ≤ 1` (`j ∈ N'`) being rows of `Ãx ≥ b̃` (`HasBoundRows`), and let
`i₁, i_j ∈ N'`. Put `P₁ := conv(P ∩ {x_{i₁} ∈ {0,1}})` and `P_{1j} := conv(P₁ ∩ {x_{i_j} ∈ {0,1}})`.
If `αx ≥ β` is valid for `P_{1j}` and `x*` is an extreme point of `P₁ ∩ {αx ≥ β}` with
`0 < x*_{i₁} < 1`, then `0 < x*_{i_j} < 1`.
Corrected: the retired version allowed an arbitrary polyhedron `Ãx ≥ b̃` without the 0-1 bounds
and arbitrary coordinates `i₁, i_j`. -/
theorem fractionality_intermediate_points_v2 {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (i1 ij : Fin n) (hi1 : i1 ∈ Nprime) (hij : ij ∈ Nprime) (α : Fin n → ℝ) (β : ℝ)
    (hValid : ∀ x ∈ SplitConvexify (SplitConvexify (Poly Atil btil) i1) ij, β ≤ dotProduct α x)
    (xstar : Fin n → ℝ)
    (hExt : xstar ∈ Set.extremePoints ℝ
      (SplitConvexify (Poly Atil btil) i1 ∩ {x | β ≤ dotProduct α x}))
    (h1 : 0 < xstar i1 ∧ xstar i1 < 1) :
    0 < xstar ij ∧ xstar ij < 1 := by sorry

end Disjunctive.LiftProject
