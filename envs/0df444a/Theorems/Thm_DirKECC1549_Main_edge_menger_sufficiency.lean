-- Prove2me | Theorems.Thm_DirKECC1549_Main_edge_menger_sufficiency
-- name    : DirKECC1549.Main.edge_menger_sufficiency
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:10:33.634591+00:00
-- url     : https://prove2.me/theorems/621c6e64-e2bf-4094-b52c-a43a074c4db4
-- title:
--   Directed edge-Menger theorem: resilience implies disjoint trails
-- statement:
--   Let $D$ be a finite directed multigraph, $x,y$ vertices and $k\ge0$. Suppose that for every set $F$ of fewer than $k$ edge identifiers there is an $x$-to-$y$ directed walk avoiding $F$. Then there are $k$ pairwise edge-disjoint directed trails from $x$ to $y$.
--
--   This is the existence direction of the directed edge form of Menger’s theorem. Parallel edges have distinct identifiers, and loops are allowed. When $x=y$, any number of empty trails suffices; when $k=0$, the empty family suffices.
-- source:
--   Directed edge-Menger theorem, EPFL Graph Theory lecture notes, Lecture 9, Section 1, https://www.epfl.ch/labs/disopt/wp-content/uploads/2019/11/GT19_notes_to_date.pdf ; also Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9. This is the existence direction for the mission's multigraph and trail encoding.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main

theorem edge_menger_sufficiency {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) (h : ∀ F : Finset (Fin m), F.card < k →
      ∃ p, IsWalk D x p y ∧ ∀ e ∈ p, e ∉ F) : HasDisjointPaths D k x y := by sorry
end DirKECC1549.Main
