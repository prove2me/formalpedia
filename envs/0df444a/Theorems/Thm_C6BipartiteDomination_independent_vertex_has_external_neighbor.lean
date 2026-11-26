-- Prove2me | Theorems.Thm_C6BipartiteDomination_independent_vertex_has_external_neighbor
-- name    : C6BipartiteDomination.independent_vertex_has_external_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:22.412636+00:00
-- url     : https://prove2.me/theorems/f654d6ba-99a5-4746-9fb5-62f9c0bf6ddf
-- title:
--   C6 Bipartite Domination: independent vertex has external neighbor
-- statement:
--   A vertex in an independent dominating set has an external neighbor when
--   the graph has no isolated vertices.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L70-L75
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L70-L75

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.independent_vertex_has_external_neighbor {D : Finset V}
    (hD : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    {v : V} (hv : v ∈ D) : ∃ w ∈ (Finset.univ \ D), G.Adj v w := by sorry
