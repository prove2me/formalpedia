-- Prove2me | Theorems.Thm_C6BipartiteDomination_bipartite_base_of_beta_eq_one
-- name    : C6BipartiteDomination.bipartite_base_of_beta_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:21.854993+00:00
-- url     : https://prove2.me/theorems/7350c12f-d16b-5eb6-92cf-6258d3a2d904
-- title:
--   C6 Bipartite Domination: bipartite base of beta eq one
-- statement:
--   With at most one `B`-neighbor, adding `w` to the bipartite graph on `B`
--   preserves bipartiteness.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L134-L190
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L134-L190

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bipartite_base_of_beta_eq_one
    {D : Finset V} {w : V}
    (hD : IsBipartiteOn G D)
    (hwD : w ∉ D)
    (hβ : betaCharge G D w = 1) :
    IsBipartiteOn G (BPart G D ∪ {w}) := by sorry
