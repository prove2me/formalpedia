-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_iterated_split_convexification_v2
-- name    : Disjunctive.HigherDim.iterated_split_convexification_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:57.270899+00:00
-- url     : https://prove2.me/theorems/04812389-a7eb-4c99-b87b-1f47941efbda
-- title:
--   Theorem 7.2 — iterating split convexification over 0-1 variables, $P_{i_1,\dots,i_t}(K) = \mathrm{conv}(K \cap \{x_{i_1},\dots,x_{i_t} \in \{0,1\}\})$
-- statement:
--   This is Theorem 7.2 of Balas's *Disjunctive Programming*. Let $K = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$), and let $i_1, \dots, i_t$ be distinct elements of $N'$. With $P_j(S) = \mathrm{conv}(S \cap \{x_j \in \{0,1\}\})$ (Theorem 7.1) and $P_{i_1,\dots,i_t}(K) := P_{i_t}(\cdots P_{i_1}(K)\cdots)$,
--
--   $$P_{i_1,\dots,i_t}(K) = \mathrm{conv}\big(K \cap \{x : x_j \in \{0,1\},\ j = i_1,\dots,i_t\}\big).$$
--
--   **Formalization Note.** The retired version allowed an arbitrary polyhedron and arbitrary coordinates; for the unbounded line $x_1 = x_0 + 1/2$ the first split creates fractional points the second split keeps. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. The coordinates of the sequence are 0-1 variables ($\in N'$), which makes the disjunctions facial as the book's proof (Theorem 3.1) requires.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.1, p. 93, Theorem 7.2

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.2 (Balas, *Disjunctive Programming*, Springer 2018, §7.1, p. 93): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`), applying the
one-variable convexification `P_j` successively along a duplicate-free sequence `i₁,…,i_t` of
0-1 indices gives `P_{i₁,…,i_t}(K) = conv(K ∩ {x : x_j ∈ {0,1}, j = i₁,…,i_t})`.
Corrected: the retired version allowed an arbitrary polyhedron `Ax ≥ b` (no bounds) and arbitrary
coordinates; the book's sequence consists of 0-1 variables of the mixed 0-1 program. -/
theorem iterated_split_convexification_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime)
    (l : List (Fin n)) (hnd : l.Nodup) (hl : ∀ j ∈ l, j ∈ Nprime) :
    IteratedSplit (Poly A b) l = convexHull ℝ (Poly A b ∩ ⋂ j ∈ l.toFinset, ZeroOneSet j) := by
  sorry

end Disjunctive.HigherDim
