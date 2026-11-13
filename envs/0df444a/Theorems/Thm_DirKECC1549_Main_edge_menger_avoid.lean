-- Prove2me | Theorems.Thm_DirKECC1549_Main_edge_menger_avoid
-- name    : DirKECC1549.Main.edge_menger_avoid
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:06:28.425137+00:00
-- url     : https://prove2.me/theorems/b5101be0-f840-4497-ad4b-1af8c6eebaf9
-- title:
--   Directed edge-Menger theorem in edge-deletion form
-- statement:
--   Let $D$ be a finite directed multigraph, $x,y$ vertices, and $k\ge0$. Then $D$ contains $k$ pairwise edge-disjoint directed trails from $x$ to $y$ if and only if, after deleting any set of fewer than $k$ edges, there remains a directed walk from $x$ to $y$:
--
--   $$
--   \text{$k$ pairwise edge-disjoint directed $x$–$y$ trails exist}
--   \quad\Longleftrightarrow\quad
--   \forall F\subseteq E(D),\ |F|<k\implies x\text{ reaches }y\text{ in }D-F.
--   $$
--
--   This is the directed edge form of Menger’s theorem, expressed in terms of resilience to edge deletion. Distinct edge identifiers account for parallel edges, and loops are allowed. If $x=y$, the empty walk and arbitrarily many empty trails satisfy both sides; if $k=0$, both sides hold vacuously.
-- source:
--   Directed edge-Menger theorem, EPFL Graph Theory lecture notes, Lecture 9, Section 1, https://www.epfl.ch/labs/disopt/wp-content/uploads/2019/11/GT19_notes_to_date.pdf ; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9. This is an edge-deletion formulation for the mission's graph encoding.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main

theorem edge_menger_avoid {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) : HasDisjointPaths D k x y ↔
    ∀ F : Finset (Fin m), F.card < k → ∃ p, IsWalk D x p y ∧
      ∀ e ∈ p, e ∉ F := by sorry
end DirKECC1549.Main
