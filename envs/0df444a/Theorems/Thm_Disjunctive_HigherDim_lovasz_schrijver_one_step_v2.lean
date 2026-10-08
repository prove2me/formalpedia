-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_lovasz_schrijver_one_step_v2
-- name    : Disjunctive.HigherDim.lovasz_schrijver_one_step_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:29.654985+00:00
-- url     : https://prove2.me/theorems/9807839f-1209-44ca-82fe-515f090eb571
-- title:
--   Theorem 7.4 — $N(K) \subseteq \mathrm{conv}(K \cap \{x_j \in \{0,1\}\})$ for every 0-1 index $j$
-- statement:
--   This is Theorem 7.4 of Balas's *Disjunctive Programming* (cited to Lovász and Schrijver [99]). Let $K = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$). Let $M(K)$ be obtained by multiplying $\tilde A x \ge \tilde b$ by $x_j$ and $1 - x_j$ for every $j \in N'$ and linearizing with one symmetric matrix $Y$ ($Y_{ij} = Y_{ji} = x_i x_j$, $Y_{jj} = x_j$ for $j \in N'$), and $N(K)$ its projection onto $x$. Then
--
--   $$N(K) \subseteq \mathrm{conv}\big(K \cap \{x : x_j \in \{0,1\}\}\big), \qquad j \in N'.$$
--
--   **Formalization Note.** The retired version allowed an arbitrary system; with no rows $N(K) = \mathbb R^n$. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. `MK`/`NOp` are unchanged and multiply all rows, bound rows included.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.2, p. 93, Theorem 7.4

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.4 (Balas, *Disjunctive Programming*, Springer 2018, §7.2, p. 93, [99]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`, so that the
Lovász-Schrijver lift multiplies them too), `N(K) ⊆ conv(K ∩ {x_j ∈ {0,1}})` for every `j ∈ N'`.
Corrected: the retired version allowed an arbitrary system `Ax ≥ b` without the bound rows. -/
theorem lovasz_schrijver_one_step_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    ∀ j ∈ Nprime, NOp A b Nprime ⊆ convexHull ℝ (Poly A b ∩ ZeroOneSet j) := by sorry

end Disjunctive.HigherDim
