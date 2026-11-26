-- Prove2me | Theorems.Thm_C6BipartiteDomination_neighbor_of_independent_outside
-- name    : C6BipartiteDomination.neighbor_of_independent_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:31.291734+00:00
-- url     : https://prove2.me/theorems/9137ce28-53be-4e4b-85aa-ea9a3f3f5ced
-- title:
--   C6 Bipartite Domination: neighbor of independent outside
-- statement:
--   If `D` is independent, a neighbor of one of its vertices lies outside it.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L63-L66
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L63-L66

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.neighbor_of_independent_outside {D : Finset V} (hD : Independent G D)
    {u v : V} (hu : u ∈ D) (hadj : G.Adj u v) : v ∉ D := by sorry
