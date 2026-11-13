-- Prove2me | Theorems.Thm_DirKECC1549_Main_edge_menger_cut
-- name    : DirKECC1549.Main.edge_menger_cut
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:14:03.985389+00:00
-- url     : https://prove2.me/theorems/aef92248-6ffd-47b6-9246-d9dde20b4cac
-- title:
--   Directed edge-Menger theorem: cut lower bounds imply disjoint trails
-- statement:
--   Let $D$ be a finite directed multigraph, $x\ne y$ vertices, and $k\ge0$. Suppose that every vertex set $S$ containing $x$ and excluding $y$ has at least $k$ outgoing edges, counted with multiplicity. Then $D$ has $k$ pairwise edge-disjoint directed trails from $x$ to $y$.
--
--   This is the cut-to-path direction of the directed edge form of Menger’s theorem. The graph may have loops and parallel edges, and the trails are lists without repeated edge identifiers.
-- source:
--   Directed edge-Menger theorem, EPFL Graph Theory lecture notes, Lecture 9, Section 1, https://www.epfl.ch/labs/disopt/wp-content/uploads/2019/11/GT19_notes_to_date.pdf ; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9. Cut-to-path direction for the mission's graph encoding.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main

theorem edge_menger_cut {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) (hxy : x ≠ y)
    (h : ∀ S : Finset (Fin n), x ∈ S → y ∉ S → k ≤ outCount D S) :
    HasDisjointPaths D k x y := by sorry
end DirKECC1549.Main
