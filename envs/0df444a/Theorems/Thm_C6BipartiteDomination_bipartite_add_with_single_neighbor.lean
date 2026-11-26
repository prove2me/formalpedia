-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartite_add_with_single_neighbor
-- name    : C6BipartiteDomination.bipartite_add_with_single_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:13.452696+00:00
-- url     : https://prove2.me/theorems/2961cc10-7ec8-5f6b-a5dd-2e5e2e4c9fdf
-- title:
--   C6 Bipartite Domination: bipartite add with single neighbor
-- statement:
--   Adding a vertex with exactly one neighbor to a bipartite induced set
--   preserves bipartiteness.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L90-L120
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L90-L120

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartite_add_with_single_neighbor
    {S : Finset V} {q u : V}
    (hS : IsBipartiteOn G S) (hu : u ∈ S) (hqu : G.Adj q u)
    (hqS : q ∉ S)
    (honly : ∀ v ∈ S, G.Adj q v → v = u) :
    IsBipartiteOn G (S ∪ {q}) := by sorry
