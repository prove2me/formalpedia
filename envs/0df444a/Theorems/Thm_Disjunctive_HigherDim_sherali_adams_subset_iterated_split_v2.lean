-- Prove2me | Theorems.Thm_Disjunctive_HigherDim_sherali_adams_subset_iterated_split_v2
-- name    : Disjunctive.HigherDim.sherali_adams_subset_iterated_split_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:07:35.271005+00:00
-- url     : https://prove2.me/theorems/96cd4116-1517-4865-85b3-9c2bf868db62
-- title:
--   Theorem 7.7 — $K_t \subseteq P_{i_1,\dots,i_t}(K)$ for any $t$ distinct 0-1 indices
-- statement:
--   This is Theorem 7.7 of Balas's *Disjunctive Programming* (Sherali–Adams [112]). Let $K = \{x : \tilde A x \ge \tilde b\}$ be the LP relaxation of a mixed 0-1 program with 0-1 index set $N'$, the system containing the bound rows $x \ge 0$ and $x_j \le 1$ ($j \in N'$), and let $K_t$ be the level-$t$ Sherali–Adams relaxation. Then for every sequence $i_1,\dots,i_t$ of distinct elements of $N'$,
--
--   $$K_t \subseteq P_{i_1,\dots,i_t}(K),$$
--
--   where $P_{i_1,\dots,i_t}(K) = P_{i_t}(\cdots P_{i_1}(K)\cdots)$ and $P_j(S) = \mathrm{conv}(S \cap \{x_j \in \{0,1\}\})$. The book states the case $i_k = k$; $K_t$ is symmetric in the indices of $N'$.
--
--   **Formalization Note.** The retired version allowed systems without the bound rows; with no rows $K_t = \mathbb R^n$. Throughout Chapter 7 the book works with $K = \{x \in \mathbb R^n : Ax \ge b,\ x \ge 0,\ x_j \le 1,\ j \in N'\} = \{x : \tilde A x \ge \tilde b\}$: the bound constraints are rows of the system that every construction multiplies. This is now the explicit hypothesis `HasBoundRows A b N'` (the system contains the rows $x_k \ge 0$ for every $k$ and $-x_j \ge -1$ for every $j \in N'$); it is satisfiable with nonempty $K$ (e.g. the unit box) and excludes the disproof's instance with no rows. The right-hand side is now the iterated operator $P_{i_1,\dots,i_t}(K)$ of the book (the retired version wrote it as $\mathrm{conv}(K \cap \{x_S \in \{0,1\}\})$, which equals it only by Theorem 7.2).
-- source:
--   E. Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §7.3, p. 95, Theorem 7.7

import Mathlib
import Definitions.Def_Disjunctive_HigherDim_Basic
import Definitions.Def_Disjunctive_HigherDim_Lifts
import Definitions.Def_Disjunctive_HigherDim_BoundRows

namespace Disjunctive.HigherDim

/-- Theorem 7.7 (Balas, *Disjunctive Programming*, Springer 2018, §7.3, p. 95, [112]): for
`K = {x : Ãx ≥ b̃}` the LP relaxation of a mixed 0-1 program with 0-1 index set `N'` (bound rows
`x ≥ 0`, `x_j ≤ 1`, `j ∈ N'`, included in the system, `HasBoundRows`, so that the Sherali-Adams
multiplication applies to them as well), `K_t ⊆ P_{i₁,…,i_t}(K)` for every duplicate-free
sequence `i₁,…,i_t` of `t` indices of `N'` (the book's statement is the case `1,…,t`; `K_t` is
symmetric in the indices of `N'`).
Corrected: the retired version allowed systems without the bound rows, and stated the right-hand
side as `conv(K ∩ {x_S ∈ {0,1}})` instead of the iterated operator `P_{i₁,…,i_t}(K)`. -/
theorem sherali_adams_subset_iterated_split_v2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (Nprime : Finset (Fin n)) (hK : HasBoundRows A b Nprime) (t : ℕ)
    (l : List (Fin n)) (hnd : l.Nodup) (hl : ∀ j ∈ l, j ∈ Nprime) (hlen : l.length = t) :
    KtSet A b Nprime t ⊆ IteratedSplit (Poly A b) l := by sorry

end Disjunctive.HigherDim
