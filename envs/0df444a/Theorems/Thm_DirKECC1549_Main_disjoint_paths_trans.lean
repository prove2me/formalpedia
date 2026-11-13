-- Prove2me | Theorems.Thm_DirKECC1549_Main_disjoint_paths_trans
-- name    : DirKECC1549.Main.disjoint_paths_trans
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T10:02:44.421718+00:00
-- url     : https://prove2.me/theorems/dd47fa1b-e456-403e-9bf1-ed91884ae31c
-- title:
--   Transitivity of directed edge-disjoint path existence
-- statement:
--   Let $D$ be a finite directed multigraph, $x,y,z$ vertices, and $k\ge 0$. If there are $k$ pairwise edge-disjoint directed trails from $x$ to $y$ and $k$ pairwise edge-disjoint directed trails from $y$ to $z$, then there are $k$ pairwise edge-disjoint directed trails from $x$ to $z$.
--
--   This directional transitivity is a consequence of the directed edge form of Menger's theorem and supports the equivalence of mutual $k$-edge-connectivity. Loops and parallel edges are permitted, and vertices need not be distinct.
-- source:
--   Derived consequence of directed edge-Menger theorem; Georgiadis et al., STOC 2027 submission #1549, Section 2 p.9 (edge connectivity and equivalence). See also https://www.epfl.ch/labs/disopt/wp-content/uploads/2019/11/GT19_notes_to_date.pdf, Lecture 9, Menger's theorem.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main

theorem disjoint_paths_trans {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y z : Fin n) (hxy : HasDisjointPaths D k x y) (hyz : HasDisjointPaths D k y z) :
    HasDisjointPaths D k x z := by sorry
end DirKECC1549.Main
