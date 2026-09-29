-- Prove2me | Theorems.Thm_Conway99_conway_99_triangle_system_of_srg
-- name    : Conway99.conway_99_triangle_system_of_srg
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-12T11:09:58.923759+00:00
-- url     : https://prove2.me/theorems/7b7c9aa0-1845-4b89-963d-d1eab1492fc5
-- title:
--   A $(99,14,1,2)$ graph yields a partial linear space of $231$ triangles
-- statement:
--   **Every $(99,14,1,2)$ graph is the collinearity graph of a partial linear space.**
--
--   Let $G$ be a strongly regular graph with parameters $(99,14,1,2)$ on a finite vertex set $P$. Since $\lambda = 1$, every edge of $G$ lies in exactly one triangle, so the triangles of $G$ behave like the *lines* of an incidence geometry. This statement asserts that the family $L$ of triangles of $G$ (three-element vertex sets that are pairwise adjacent) has the four defining properties of the line-system form of Conway's 99-graph problem:
--
--   1. every line has exactly three points, $|l| = 3$ for $l \in L$;
--   2. two distinct lines meet in at most one point, $|l_1 \cap l_2| \le 1$;
--   3. every point lies on exactly seven lines;
--   4. any two distinct points $x \ne y$ lying on no common line satisfy
--   $$\bigl|\{ z \in P : z \ne x,\ z \ne y,\ (\exists l \in L,\ x, z \in l),\ (\exists l \in L,\ y, z \in l) \}\bigr| = 2 .$$
--
--   Property (2) is the uniqueness of the triangle on an edge, which is $\lambda = 1$. Property (3) is the local structure at a vertex: the neighbourhood of $x$ carries a perfect matching, since each of the $14$ neighbours of $x$ is adjacent to exactly one other neighbour of $x$; counting the incidences between neighbours of $x$ and triangles through $x$ gives $2\,|L_x| = 14$, so $|L_x| = 7$. Property (4) is $\mu = 2$ together with the observation that two distinct points are collinear if and only if they are adjacent.
--
--   Together with the converse implication, this makes the line-system statement an equivalent form of Conway's 99-graph problem: it is the form in which the problem is usually attacked computationally, and the direction proved here is the one needed to derive consequences from a hypothetical $(99,14,1,2)$ graph.
--
--   *Formalization note.* The vertex type is an arbitrary finite type with decidable equality; the parameters $(99,14,1,2)$ enter only through the degree $14$, $\lambda = 1$ and $\mu = 2$.
-- source:
--   J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1); the partial linear space (locally linear graph) description of a strongly regular graph with lambda = 1 is standard, see https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem, and the mission milestone Conway99.conway_99_cliqueFinset_three_card (231 triangles).

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open Finset SimpleGraph

namespace Conway99

theorem conway_99_triangle_system_of_srg {V : Type} [Fintype V] [DecidableEq V]
    (g : SimpleGraph V) [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) :
    ∃ L : Finset (Finset V),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : V, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : V, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (univ.filter fun z : V => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2) := by sorry

end Conway99
