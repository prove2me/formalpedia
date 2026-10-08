-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_construction_regular
-- name    : ExplicitExpanders.Delete.construction_regular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:15:43.33382+00:00
-- url     : https://prove2.me/theorems/986122c2-4eec-435c-a266-22274897e7db
-- title:
--   Proof of Theorem 1.3 — $G = H'+M$ is $d$-regular on $|V|-|U|$ vertices and $A_G = A_{H'}+A_M$
-- statement:
--   Let $H$ be a finite $d$-regular graph on $V$ and $r\ge 1$. Let $U\subseteq V$ satisfy the conclusions 2 and 3 of Lemma 3.1: the $(r+1)$-neighbourhood of every vertex of $U$ contains no cycle, and distinct vertices of $U$ are at distance at least $2r+3$. Let $m$ be a perfect matching on $N(U)$, and let $G = H' \cup M$ be the graph obtained by omitting $U$ and adding the matching edges $\{x, m(x)\}$, $x \in N(U)$. Then
--
--   1. $G$ is $d$-regular;
--   2. $G$ has $|V| - |U|$ vertices;
--   3. $$A_G = A_{H'} + A_M .$$
--
--   This is the sentence "Clearly it is $d$-regular and has $n$ vertices" and the note "$A_G = A_{H'} + A_M$" in the proof of Theorem 1.3 (p. 13). Item 3 says that no matching pair is already an edge of $H'$.
--
--   **Formalization Note** The hypothesis $r\ge1$ is the case used by Theorem 1.3, where $r = \lceil 2/\varepsilon\rceil \ge 1$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 13, proof of Theorem 1.3 ("Clearly it is d-regular and has n vertices"; "Note that A_G = A_{H′} + A_M")

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch

namespace ExplicitExpanders.Delete

open Matrix

open Classical in
/-- Proof of Theorem 1.3 (Alon, arXiv:2003.11673v1, p. 13): under the conclusions 2–3 of
Lemma 3.1 (with `r ≥ 1`), omitting `U` and adding a perfect matching on `N(U)` gives a
`d`-regular graph on `|V| - |U|` vertices with `A_G = A_{H'} + A_M`. -/
theorem construction_regular {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d r : ℕ) (hreg : H.IsRegularOfDegree d) (hr : 1 ≤ r)
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (r + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    (deleteAndMatch H U m).IsRegularOfDegree d ∧
      Fintype.card (Kept U) = Fintype.card V - U.card ∧
      (deleteAndMatch H U m).adjMatrix ℝ =
        (deleted H U).adjMatrix ℝ + (matchGraph H U m).adjMatrix ℝ := by sorry

end ExplicitExpanders.Delete
