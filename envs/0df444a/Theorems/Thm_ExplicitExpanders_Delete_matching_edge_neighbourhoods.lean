-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_matching_edge_neighbourhoods
-- name    : ExplicitExpanders.Delete.matching_edge_neighbourhoods
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:15:45.355507+00:00
-- url     : https://prove2.me/theorems/a3143c0c-8f5b-4ac9-a684-38d7922c2d97
-- title:
--   Proof of Theorem 1.3 — matching edges have cycle-free $(r-1)$-neighbourhoods and disjoint $r$-neighbourhoods
-- statement:
--   Let $H$ be a finite graph on $V$, $r \ge 1$, and let $U\subseteq V$ satisfy the conclusions 2 and 3 of Lemma 3.1: the $(r+1)$-neighbourhood of every vertex of $U$ contains no cycle, and distinct vertices of $U$ are at distance at least $2r+3$. Let $m$ be a perfect matching on $N(U)$ and $G = H'\cup M$ the resulting graph. Then, with all neighbourhoods and distances taken in $G$:
--
--   1. for every edge $xy$ of $M$, the $(r-1)$-neighbourhood of $xy$ contains no cycle;
--   2. for any two distinct edges $xy$ and $x'y'$ of $M$, the $r$-neighbourhoods of $xy$ and of $x'y'$ are disjoint.
--
--   The paper states: "Note that the $r$-neighborhood of any edge $uv$ of the added matching $M$ contains no cycle", and before (11), "Since all these neighborhoods are pairwise disjoint". The first claim, with the $r$-neighbourhood, fails in a boundary case: if $z_1,z_2 \in U$ are at distance exactly $2r+3$ and the matching joins $a\in N(z_1)$ to $b\in N(z_2)$, both on a shortest $z_1z_2$ path, then the middle edge of the $a$–$b$ path joins two vertices at distance $r$ from $\{a,b\}$, and the induced subgraph on the $r$-neighbourhood of $ab$ contains a cycle. The statement here uses the $(r-1)$-neighbourhood, which suffices: Lemma 3.2 on the $r$ layers $N_0,\dots,N_{r-1}$ gives $f^2(x)+f^2(y) \le \frac1r\sum_{w} f^2(w)$ over the $(r-1)$-neighbourhood, exactly the factor $1/r$ used in (11).
--
--   **Formalization Note** "Distinct edges" is inequality of the unordered pairs `s(x, y) ≠ s(x', y')`. Since $r\ge1$, $r-1$ is ordinary subtraction.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 13, proof of Theorem 1.3 ("Note that the r-neighborhood of any edge uv of the added matching M contains no cycle"; "Since all these neighborhoods are pairwise disjoint"), corrected to the (r−1)-neighbourhood

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

/-- Proof of Theorem 1.3 (Alon, arXiv:2003.11673v1, p. 13), the note on the matching edges, in
corrected form: in `G = H' + M` the `(r-1)`-neighbourhood of every edge of `M` contains no cycle,
and the `r`-neighbourhoods of distinct edges of `M` are disjoint. (The printed claim, with the
`r`-neighbourhood, fails when two vertices of `U` are at distance exactly `2r+3`.) -/
theorem matching_edge_neighbourhoods {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (r : ℕ) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    (∀ x y : Kept U, (matchGraph H U m).Adj x y →
        NoCycleOn (deleteAndMatch H U m) (edgeBall (deleteAndMatch H U m) x y (r - 1))) ∧
    (∀ x y x' y' : Kept U, (matchGraph H U m).Adj x y → (matchGraph H U m).Adj x' y' →
        s(x, y) ≠ s(x', y') →
        Disjoint (edgeBall (deleteAndMatch H U m) x y r)
          (edgeBall (deleteAndMatch H U m) x' y' r)) := by sorry

end ExplicitExpanders.Delete
