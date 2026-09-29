-- Prove2me | Theorems.Thm_Conway99_triangle_system_iff_adjacency_matrix
-- name    : Conway99.triangle_system_iff_adjacency_matrix
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-25T07:44:51.45125+00:00
-- url     : https://prove2.me/theorems/77e0379f-da84-4d77-8a0d-24d42e6e1764
-- title:
--   Conway 99 triangle system and adjacency matrix formulations are equivalent
-- statement:
--   Equivalence of the two Conway 99-graph formulations.
--
--   Conway's 99-graph problem asks whether a strongly regular graph with parameters (99,14,1,2) exists — open since the 1960s. The mission ships it in two forms: (A) the adjacency-matrix form, asserting a 99x99 0/1 symmetric zero-diagonal matrix A with A^2 + A = 12I + 2J, and (B) the triangle line-system (partial linear space) form, asserting a family L of 3-point lines on 99 points with pairwise intersections <= 1, exactly 7 lines through each point, and exactly 2 further points simultaneously collinear with each non-collinear pair. This theorem states that these two existence claims are equivalent: the triangles of a graph with lambda = 1 assemble into exactly such a line system, and the collinearity graph of such a line system is 14-regular with adjacent pairs sharing one common neighbour and non-adjacent pairs sharing two — i.e. it satisfies the matrix equation. Both leaves' own natural-language statements sketch the proof in both directions (two-path counting on one side, triangle decomposition on the other).
--
--   This equivalence is the only solvable-shaped node in the Conway99 mission: the two leaves themselves ARE the 60-year-open existence problem (an existence proof needs a witness unknown to mathematics; a nonexistence proof would settle the problem outright), so no worker can attack them directly. The equivalence, by contrast, is elementary finite combinatorics about the relationship between the two formulations — genuinely provable — and publishing it wires both open leaves together in the mission graph.
-- source:
--   J. H. Conway, 'Five $1,000 Problems (Update 2017)', OEIS, https://oeis.org/A248380/a248380.pdf (Problem 1); equivalence of the adjacency-matrix formulation (A. E. Brouwer and W. H. Haemers, 'Spectra of Graphs', Springer 2012, Section 9.1) and the partial linear space formulation (https://en.wikipedia.org/wiki/Conway%27s_99-graph_problem); connects mission theorems Conway99.conway_99_adjacency_matrix_exists (c4d343fc-712e-432f-9820-bdb95039c39d) and Conway99.conway_99_triangle_system_exists (f0530c39-57be-49db-9612-c8e755b8b545).

import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open scoped BigOperators

namespace Conway99

theorem triangle_system_iff_adjacency_matrix :
    (∃ L : Finset (Finset (Fin 99)),
      (∀ l ∈ L, l.card = 3) ∧
      (∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ≠ l₂ → (l₁ ∩ l₂).card ≤ 1) ∧
      (∀ x : Fin 99, (L.filter fun l => x ∈ l).card = 7) ∧
      (∀ x y : Fin 99, x ≠ y → (∀ l ∈ L, ¬(x ∈ l ∧ y ∈ l)) →
        (Finset.univ.filter fun z : Fin 99 => z ≠ x ∧ z ≠ y ∧
            (∃ l ∈ L, x ∈ l ∧ z ∈ l) ∧ (∃ l ∈ L, y ∈ l ∧ z ∈ l)).card = 2))
    ↔
    (∃ A : Matrix (Fin 99) (Fin 99) ℕ,
      (∀ i j, A i j = 0 ∨ A i j = 1) ∧
      (∀ i j, A i j = A j i) ∧
      (∀ i, A i i = 0) ∧
      (∀ i j, (∑ k, A i k * A k j) + A i j = (if i = j then 12 else 0) + 2)) := by sorry

end Conway99
