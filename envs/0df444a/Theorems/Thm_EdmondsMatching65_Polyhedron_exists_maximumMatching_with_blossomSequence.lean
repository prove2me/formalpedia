-- Prove2me | Theorems.Thm_EdmondsMatching65_Polyhedron_exists_maximumMatching_with_blossomSequence
-- name    : EdmondsMatching65.Polyhedron.exists_maximumMatching_with_blossomSequence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:45:03.270209+00:00
-- url     : https://prove2.me/theorems/7398c825-24ae-4e06-8004-6078c8d80e02
-- title:
--   §6, p. 128 — for every weight vector there is some maximum matching with a sequence {G_i}
-- statement:
--   Let $G$ be a finite graph and $c\in\mathbb R^E$ any real edge weights. Then there exists a matching $M$ which is maximum for $c$ and for which a sequence $\{G_i\}$ satisfying conditions (a)–(k) of Theorem (M) exists.
--
--   This is what the weighted matching algorithm of §7 produces (the "simpler construction"); together with the §5 translation it yields an optimality certificate for every weight vector, which is all that Theorem (P) needs.
--
--   **Formalization Note** The graph is given by a finite node type $V$, a finite edge type $E$ and, for each edge, the unordered pair of its ends (no loops). Parallel edges are allowed, which covers the contracted graphs of Theorem (M); a simple graph is the special case of an injective end map. Vectors $x$ have one real coordinate per edge.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), p. 128, §6, second paragraph

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_EdmondsMatching65_Polyhedron_BlossomSequence

namespace EdmondsMatching65.Polyhedron

theorem exists_maximumMatching_with_blossomSequence {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : Graph V E) (c : E → ℝ) :
    ∃ M : Finset E, IsMaximumMatching G c M ∧ Nonempty (BlossomSequence G c M) := by sorry

end EdmondsMatching65.Polyhedron
