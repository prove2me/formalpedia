-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartite_replacement_of_base
-- name    : C6BipartiteDomination.bipartite_replacement_of_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:08.759165+00:00
-- url     : https://prove2.me/theorems/efc13e02-5ec8-57b8-8dd8-e43328847547
-- title:
--   C6 Bipartite Domination: bipartite replacement of base
-- statement:
--   A two-colouring of `B ∪ {w}` extends over the retained isolated selected
--   vertices after replacing a subset of `Z₀` by `w`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L73-L130
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L73-L130

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartite_replacement_of_base
    {D X : Finset V} {w : V}
    (hX : X ⊆ ZPart G D) (hwD : w ∉ D)
    (hbase : IsBipartiteOn G (BPart G D ∪ {w})) :
    IsBipartiteOn G ((D \ X) ∪ {w}) := by sorry
