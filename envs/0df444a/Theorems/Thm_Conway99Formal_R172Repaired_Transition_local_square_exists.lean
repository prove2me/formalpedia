-- Prove2me | Theorems.Thm_Conway99Formal_R172Repaired_Transition_local_square_exists
-- name    : Conway99Formal.R172Repaired.Transition.local_square_exists
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:16:01.958329+00:00
-- url     : https://prove2.me/theorems/917f2b6c-1fb5-48f6-a9a4-83f547535741
-- title:
--   A conditional induced square in an R172 transition packet
-- statement:
--   Let G be an actual strongly regular graph with parameters (99,14,1,2), and suppose p is a Transition packet in G satisfying the explicit R170–R171 data: a 36-vertex support, a disjoint 3-vertex clique, the complementary 60-vertex zero-support set, a support centre adjacent to two distinct nonadjacent outer vertices in that zero-support set, the stated row-codegree cap, exclusion of triangle common neighbors, zero-transport at the centre, and nonadjacency of any second common support point to the centre. Then the centre and the two outer vertices can be completed by a fourth vertex to form an induced 4-cycle. This is a conditional local result: constructing p from a uniform-empty branch is a separate open obligation; it does not prove that such a branch or graph exists. The converse from q=1 to a core connector is withdrawn.
-- source:
--   Conway99/results/R172_uniform_empty_active_transition_squares.md (SHA-256 983d75aa77e82152d4eb32655c8e05a6f00e81d082877fa69d80b668f529ef85); formalization/2026-10-03/r172-repaired/R172Repaired.lean at a45708acebe3f397faccb1b646be906f24f23ee5 (Git blob 581e8b0a310649acd6868745deb8cabcbc55026c). Finite replay: replays/odd-cross-lift/UNIFORM_EMPTY_ACTIVE_TRANSITION_SQUARE_CHECK.py. The result is conditional on an explicit R170–R171 Transition packet.

import Mathlib
import Definitions.Def_r172_repaired
set_option autoImplicit false
open SimpleGraph Finset
open Conway99Formal.R172Repaired

theorem Conway99Formal.R172Repaired.Transition.local_square_exists {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (p : Transition G) (h : G.IsSRGWith 99 14 1 2) : ∃ x, p.inducedSquare x := by sorry
