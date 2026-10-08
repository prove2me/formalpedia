-- Prove2me | Theorems.Thm_ChinesePostman_Matching_exists_euler_tour
-- name    : ChinesePostman.Matching.exists_euler_tour
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:40:12.793982+00:00
-- url     : https://prove2.me/theorems/3a780c8a-7072-453e-bd06-475baa03e2bf
-- title:
--   §2, p. 89 — Euler tour of a connected even multigraph
-- statement:
--   Let $G$ be a finite connected loopless multigraph with at least one node. If every node has even degree, there is a closed walk using each named edge exactly once:
--
--   $$
--   (\forall v\in N,\ \deg_G(v)\equiv0\pmod2)
--   \quad\Longrightarrow\quad
--   \exists\text{ an Euler tour of }G.
--   $$
--
--   The result applies to the graph obtained by adding copies of original edges, where parallel edges must be distinguished.
--
--   **Formalization Note** Nonemptiness of the node set is explicit because a list-based tour has a starting node; the zero-edge tour at a single node is permitted.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 89, §2, Euler-tour paragraph, https://doi.org/10.1007/BF01580113

import Mathlib
import Definitions.Def_ChinesePostman_Matching_Setting

namespace ChinesePostman.Matching


/-- §2, p. 89: a connected even-degree multigraph has an Euler tour. -/
theorem exists_euler_tour
    {V E : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : EdmondsMatching65.Polyhedron.Graph V E) (hG : Connected G)
    (heven : ∀ v, Even (degree G v)) :
    ∃ ns : List V, ∃ es : List E, IsEulerTour G ns es := by sorry
end ChinesePostman.Matching
