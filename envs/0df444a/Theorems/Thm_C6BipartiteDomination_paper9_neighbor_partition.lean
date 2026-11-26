-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_neighbor_partition
-- name    : C6BipartiteDomination.paper9_neighbor_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:26.369634+00:00
-- url     : https://prove2.me/theorems/c90b8bc2-d9c2-502a-b705-1e40f2f3e662
-- title:
--   C6 Bipartite Domination: paper9 neighbor partition
-- statement:
--   The neighbors of a selected `B`-vertex split into its selected neighbors,
--   its private external neighbors, and its `S`-neighbors.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L76-L118
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L76-L118

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_neighbor_partition
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {u : V} (huB : u ∈ BPart G D) :
    (Finset.univ.filter fun q => G.Adj u q) =
      (D.filter fun q => G.Adj u q) ∪
        (privateExternalNeighbors G D u ∪
          (SPart G D).filter fun q => G.Adj u q) := by sorry
