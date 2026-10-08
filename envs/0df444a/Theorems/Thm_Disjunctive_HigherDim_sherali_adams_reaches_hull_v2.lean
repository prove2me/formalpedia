-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_sherali_adams_reaches_hull_v2
-- name    : Disjunctive.HigherDim.sherali_adams_reaches_hull_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:14.095515+00:00
-- url     : https://prove2.me/theorems/52cce9a3-0396-4999-bd8a-5a573e422a41
-- title:
--   Theorem 7.6 — the Sherali–Adams hierarchy reaches the integer hull, $K_p = \mathrm{conv}(K_0)$
-- statement:
--   This is Theorem 7.6 of Balas's *Disjunctive Programming* (cited to Sherali and Adams [112]). Let $K = \{x \in \mathbb R^n : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program whose 0-1 variables are indexed by $N'$, $|N'| = p$, where the system $\tilde A x \ge \tilde b$ contains the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$), and let $K_0 = K \cap \{x : x_j \in \{0,1\},\ j \in N'\}$. Let $K_t$ be the level-$t$ Sherali–Adams relaxation: multiply every row of $\tilde A x \ge \tilde b$ by every product $\prod_{j \in J_1} x_j \prod_{j \in J_2}(1 - x_j)$ with $J_1, J_2 \subseteq N'$ disjoint, $|J_1 \cup J_2| = t$, linearize the monomials with moment variables (using $x_j^2 = x_j$ for $j \in N'$) and project onto $x$. Then
--
--   $$K_p = \mathrm{conv}(K_0).$$
--
--   **Formalization Note.** The retired version allowed an arbitrary system $Ax \ge b$; with no rows, $K_p = \mathbb R^n$ while $\mathrm{conv}(K_0)$ lies in the unit box. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. The definitions `KtSet`/`IsXt`/`RowNLt` are unchanged: they multiply all rows of the given system, hence the bound rows too, exactly as the book multiplies $\tilde A x \ge \tilde b$.
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.3, p. 95, Theorem 7.6

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.6 (Balas, *Disjunctive Programming*, Springer 2018, §7.3, p. 95, [112]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with `p = |N'|` 0-1 variables (bound
rows `x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`, so that the
Sherali-Adams multiplication applies to them as well), the top level of the Sherali-Adams
hierarchy is the integer hull: `K_p = conv(K₀)`.
Corrected: the retired version allowed systems without the bound rows, for which `K_p` need not
lie in the unit box. -/
theorem sherali_adams_reaches_hull_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) :
    KtSet A b Nprime Nprime.card = convexHull ℝ (K0Set A b Nprime) := by sorry

end Disjunctive.HigherDim
