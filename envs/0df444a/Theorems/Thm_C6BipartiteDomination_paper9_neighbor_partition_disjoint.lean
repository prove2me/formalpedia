-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_neighbor_partition_disjoint
-- name    : C6BipartiteDomination.paper9_neighbor_partition_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:41.217707+00:00
-- url     : https://prove2.me/theorems/aa6c7cbd-7924-561f-a23b-a73b4f34eaf6
-- title:
--   C6 Bipartite Domination: paper9 neighbor partition disjoint
-- statement:
--   The three parts in the neighbor partition are pairwise disjoint.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L121-L142
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L121-L142

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_neighbor_partition_disjoint
    {D : Finset V} {u : V} (huB : u ∈ BPart G D) :
    Disjoint (D.filter fun q => G.Adj u q)
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) ∧
    Disjoint (privateExternalNeighbors G D u)
        ((SPart G D).filter fun q => G.Adj u q) := by sorry
