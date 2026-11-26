-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper10_z0_has_S_neighbor
-- name    : C6BipartiteDomination.paper10_z0_has_S_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:45.940797+00:00
-- url     : https://prove2.me/theorems/292ab4d2-8621-454e-909a-41f8aef16029
-- title:
--   C6 Bipartite Domination: paper10 z0 has S neighbor
-- statement:
--   Every `Z₀` vertex has an `S`-neighbor, provided the ambient graph has no
--   isolated vertices. The fact that it has no selected neighbors follows from
--   its membership in `Z`; a `W₀` neighbor is excluded by the definition of `Z₀`;
--   and a private `P`-neighbor would force the vertex into `B`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L87-L109
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L87-L109

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper10_z0_has_S_neighbor
    {D : Finset V} (hNoIso : HasNoIsolatedVertices G) {z : V}
    (hz : z ∈ Z0Part G D) :
    ∃ q ∈ SPart G D, G.Adj z q := by sorry
