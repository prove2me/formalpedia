-- Prove2me | solution 1 for deBruijn_erdos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:50.232052+00:00
-- url     : https://prove2.me/submissions/3c2bf5a3-247f-49a3-885f-17c65b0fe1d2

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Compactness
import Definitions.Def_Polychromatic_Compactness
import Theorems.Thm_nonempty_hom_of_forall_finite_subgraph_hom

set_option autoImplicit true

theorem _root_.solution {α β : Type*} (G : SimpleGraph α) [Finite β]
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Coloring β) : Nonempty (G.Coloring β) :=
  nonempty_hom_of_forall_finite_subgraph_hom h
