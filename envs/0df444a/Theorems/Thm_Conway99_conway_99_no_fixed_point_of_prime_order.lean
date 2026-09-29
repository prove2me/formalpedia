-- Prove2me | Theorems.Thm_Conway99_conway_99_no_fixed_point_of_prime_order
-- name    : Conway99.conway_99_no_fixed_point_of_prime_order
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-06T18:31:41.797223+00:00
-- url     : https://prove2.me/theorems/672f926d-ea1a-441e-951e-260e5f541f03
-- title:
--   Wilbrink: an automorphism of prime order $p>7$ of a $(99,14,1,2)$ graph is fixed-point-free
-- statement:
--   Let $G$ be a strongly regular graph with parameters $(n,k,\lambda,\mu)=(99,14,1,2)$: it has $99$ vertices, every vertex has $14$ neighbours, two adjacent vertices have exactly one common neighbour, and two distinct non-adjacent vertices have exactly two common neighbours.
--
--   Let $p$ be a prime with $p>7$ and let $\sigma$ be an automorphism of $G$ of order exactly $p$. Then $\sigma$ fixes no vertex:
--
--   $$\sigma(v)\neq v \qquad \text{for every vertex } v .$$
--
--   Since $\lambda=1$, the graph carries the structure of a partial linear space whose lines are the triangles; each vertex lies on $7$ lines. The statement is the first step in the analysis of the possible automorphisms of a hypothetical $99$-graph: it forces the orbits of $\sigma$ to all have length $p$, so that $p \mid 99$ and hence $p=11$.
--
--   **Formalization Note** The order of $\sigma$ in the automorphism group $g \simeq_g g$ is expressed with `orderOf`; the group structure is the one Mathlib puts on self-isomorphisms of a relation.
-- source:
--   H. A. Wilbrink, 'On the (99,14,1,2) strongly regular graph', in: Papers dedicated to J. J. Seidel (P. J. de Doelder, J. de Graaf, J. H. van Lint, eds.), EUT Report 84-WSK-03, Eindhoven University of Technology, 1984, pp. 342-355, https://pure.tue.nl/ws/files/2449333/256699.pdf ; Section 3, p. 349 (first paragraph)

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Order.Group.End
import Mathlib.GroupTheory.OrderOfElement

open SimpleGraph

namespace Conway99

theorem conway_99_no_fixed_point_of_prime_order {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] (h : g.IsSRGWith 99 14 1 2) {p : ℕ} (hp : p.Prime) (hp7 : 7 < p)
    (σ : g ≃g g) (hσ : orderOf σ = p) (v : V) : σ v ≠ v := by sorry

end Conway99
