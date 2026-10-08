-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_full_split_convexification_v2
-- name    : Disjunctive.HigherDim.full_split_convexification_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:01.325994+00:00
-- url     : https://prove2.me/theorems/ff1dd025-d6fc-492e-a4dd-e685feb11706
-- title:
--   Corollary 7.3 — iterating over every 0-1 index reaches the integer hull, $P_{1,\dots,p}(K) = \mathrm{conv}(K_0)$
-- statement:
--   This is Corollary 7.3 of Balas's *Disjunctive Programming*. Let $K = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$), and $K_0 = K \cap \{x : x_j \in \{0,1\},\ j \in N'\}$. Applying $P_j(S) = \mathrm{conv}(S \cap \{x_j \in \{0,1\}\})$ successively for every $j \in N'$ (in any order, each once) gives
--
--   $$P_{1,\dots,p}(K) = \mathrm{conv}(K_0).$$
--
--   **Formalization Note.** The retired version allowed an arbitrary polyhedron, for which the statement fails (unbounded line $x_1 = x_0 + 1/2$). Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.1, p. 93, Corollary 7.3

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Corollary 7.3 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 93): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`), iterating the
one-variable convexification over all of `N'` (in any duplicate-free order) gives
`P_{1,…,p}(K) = conv(K₀)`.
Corrected: the retired version allowed an arbitrary polyhedron `Ax ≥ b` without the bounds. -/
theorem full_split_convexification_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (l : List (Fin n)) (hnd : l.Nodup)
    (heq : l.toFinset = Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (K0Set A b Nprime) := by sorry

end Disjunctive.HigherDim
