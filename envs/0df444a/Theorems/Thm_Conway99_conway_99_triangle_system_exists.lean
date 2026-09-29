-- Prove2me | Theorems.Thm_Conway99_conway_99_triangle_system_exists
-- name    : Conway99.conway_99_triangle_system_exists
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-12T11:03:20.209358+00:00
-- url     : https://prove2.me/theorems/f0530c39-57be-49db-9612-c8e755b8b545
-- title:
--   Line-system form of Conway's 99-graph problem: $99$ points, $231$ lines of size $3$
-- statement:
--   **Line-system (partial linear space) form of Conway's 99-graph problem.**
--
--   A graph that is strongly regular with parameters $(99,14,1,2)$ has $\lambda = 1$, so every edge lies in a unique triangle and the $693$ edges are partitioned into $231$ triangles. Reading the triangles as *lines*, such a graph is exactly the collinearity graph of a partial linear space on $99$ points whose lines have three points each. This statement asserts the existence of that incidence structure.
--
--   Concretely, the assertion is that there is a family $L$ of subsets of a $99$-element point set $P$ (the lines) with the following four properties.
--
--   1. Every line has exactly three points: $|l| = 3$ for all $l \in L$.
--   2. Two distinct lines meet in at most one point: $|l_1 \cap l_2| \le 1$ for distinct $l_1, l_2 \in L$.
--   3. Every point lies on exactly seven lines: $|\{ l \in L : x \in l \}| = 7$ for all $x \in P$.
--   4. Any two distinct points $x \ne y$ lying on no common line are simultaneously collinear with exactly two further points; that is,
--   $$\bigl|\{ z \in P : z \ne x,\ z \ne y,\ (\exists l \in L,\ x, z \in l),\ (\exists l \in L,\ y, z \in l) \}\bigr| = 2 .$$
--
--   Call two distinct points *collinear* when some line contains both, and let $G$ be the resulting collinearity graph. Conditions (1)-(3) make $G$ regular of degree $14$: the seven lines through a point $x$ contribute two neighbours each, and by (2) no neighbour is counted twice. Condition (4) says that two distinct non-adjacent vertices of $G$ have exactly two common neighbours. The remaining strong-regularity condition, that adjacent vertices have exactly one common neighbour, is *not* assumed here: it follows from (1)-(4) by counting the paths of length two leaving a fixed vertex. Hence the existence of such a line system is sufficient for the existence of a strongly regular graph with parameters $(99,14,1,2)$, and it is also necessary, the lines being the triangles of such a graph.
--
--   No such line system is known, and none is known not to exist; the statement carries the full open content of Conway's 99-graph problem.
-- source:
--   J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1). The partial-linear-space reformulation (a (99,14,1,2) graph has every edge in a unique triangle, so its 693 edges split into 231 triangles of a partial linear space on 99 points with 7 lines through each point) is the standard one, see https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem and the mission milestone Conway99.conway_99_cliqueFinset_three_card.

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open Finset

namespace Conway99

theorem conway_99_triangle_system_exists :
    ∃ L : Finset (Finset (Fin 99)),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2) := by sorry

end Conway99
