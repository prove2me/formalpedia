-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lift_and_project_one_var_v2
-- name    : Disjunctive.HigherDim.lift_and_project_one_var_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:06.584719+00:00
-- url     : https://prove2.me/theorems/6254dfdf-81c7-428d-9146-2b58e00a61ad
-- title:
--   Theorem 7.1 — the nonlinear 3-step lift-and-project equals split convexification, $P_j(K) = \mathrm{conv}(K \cap \{x_j \in \{0,1\}\})$
-- statement:
--   This is Theorem 7.1 of Balas's *Disjunctive Programming*. Let $K = \{x \in \mathbb R^n : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$), and let $j \in N'$. Multiply $\tilde A x \ge \tilde b$ by $1 - x_j$ and by $x_j$, linearize $y_i := x_i x_j$ ($i \ne j$) and $x_j^2 := x_j$, obtaining $M_j(K)$, and let $P_j(K)$ be its projection onto $x$. Then
--
--   $$P_j(K) = \mathrm{conv}\big(K \cap \{x : x_j \in \{0,1\}\}\big).$$
--
--   **Formalization Note.** The retired version allowed an arbitrary system $Ax \ge b$ and an arbitrary coordinate $j$; with no rows, $P_j(K) = \mathbb R^n$ while the hull lies in $0 \le x_j \le 1$. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. The coordinate $j$ is a 0-1 variable ($j \in N'$), as in the book.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.1, p. 92, Theorem 7.1

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.1 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 92): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (the bound
rows `x ≥ 0` and `x_j ≤ 1`, `j ∈ N'`, are rows of the system, `HasBoundRows`) and `j ∈ N'`, the
projection `P_j(K)` of the nonlinear 3-step construction (multiply `Ãx ≥ b̃` by `1 - x_j` and
`x_j`, linearize, project) equals `conv(K ∩ {x_j ∈ {0,1}})`.
Corrected: the retired version allowed an arbitrary system `Ax ≥ b`, without the bound rows the
book folds into `Ãx ≥ b̃`, and an arbitrary coordinate `j`. -/
theorem lift_and_project_one_var_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (j : Fin n) (hj : j ∈ Nprime) :
    Pj A b j = convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
