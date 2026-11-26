-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartite_add_independent_set_at_vertex
-- name    : C6BipartiteDomination.bipartite_add_independent_set_at_vertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:14.231014+00:00
-- url     : https://prove2.me/theorems/1d0f3a6c-64a0-513e-a695-97bfc99a7f0b
-- title:
--   C6 Bipartite Domination: bipartite add independent set at vertex
-- statement:
--   An independent set whose only possible edges into a bipartite base meet a
--   single vertex can be added by assigning it the opposite color.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L469-L498
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L469-L498

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartite_add_independent_set_at_vertex
    {S U : Finset V} {w : V}
    (hS : IsBipartiteOn G S) (hwS : w ∈ S)
    (hU : Independent G U) (hwU : w ∉ U)
    (hdisj : Disjoint S U)
    (hboundary : ∀ ⦃u v⦄, u ∈ U → v ∈ S → G.Adj u v → v = w) :
    IsBipartiteOn G (S ∪ U) := by sorry
