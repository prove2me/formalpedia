-- Prove2me | Theorems.Thm_ExplicitExpanders_Delete_lemma_3_1
-- name    : ExplicitExpanders.Delete.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:14:40.317792+00:00
-- url     : https://prove2.me/theorems/b5c07b60-2996-424c-8c7b-f2446e10e259
-- title:
--   Lemma 3.1 — many far-apart vertices with cycle-free $(r+1)$-neighbourhoods
-- statement:
--   Let $G=(V,E)$ be a $d$-regular graph on $n$ vertices with $d \ge 3$, and let $r \ge 0$ be an integer with $r \le \log_{d-1} n$. Suppose that the $(2r+4)$-neighbourhood of every vertex contains at most one cycle. Then there is a set $U \subseteq V$ such that
--
--   1. $$|U| \ge \frac{n}{2d^{2r+3}};$$
--   2. the $(r+1)$-neighbourhood of every vertex of $U$ contains no cycle;
--   3. any two distinct vertices of $U$ are at distance at least $2r+3$.
--
--   This lemma supplies the vertices that are deleted in the construction of Theorem 1.3: they are far from all short cycles and far from each other.
--
--   **Formalization Note** "Contains at most one cycle" and "contains no cycle" refer to the induced subgraphs on the balls (see the definition `Neighbourhoods`); distances are extended distances, so vertices in different components are at distance $\infty$. The paper also states that $U$ can be found in polynomial time; this algorithmic claim is not formalized.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 10, Lemma 3.1

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods

namespace ExplicitExpanders.Delete

/-- Lemma 3.1 (Alon, arXiv:2003.11673v1, p. 10). The polynomial-time claim is not formalized. -/
theorem lemma_3_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d r : ℕ) (hd : 3 ≤ d) (hreg : G.IsRegularOfDegree d)
    (hcyc : ∀ v : V, AtMostOneCycleOn G (ball G v (2 * r + 4)))
    (hr : (r : ℝ) ≤ Real.logb ((d : ℝ) - 1) (Fintype.card V)) :
    ∃ U : Finset V,
      (Fintype.card V : ℝ) / (2 * (d : ℝ) ^ (2 * r + 3)) ≤ (U.card : ℝ) ∧
      (∀ z ∈ U, NoCycleOn G (ball G z (r + 1))) ∧
      (∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * r + 3 : ℕ) : ℕ∞) ≤ G.edist z z') := by sorry

end ExplicitExpanders.Delete
