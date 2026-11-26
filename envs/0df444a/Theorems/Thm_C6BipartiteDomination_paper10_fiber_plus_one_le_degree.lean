-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper10_fiber_plus_one_le_degree
-- name    : C6BipartiteDomination.paper10_fiber_plus_one_le_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:19.704847+00:00
-- url     : https://prove2.me/theorems/c78b6dcc-3d14-4da9-ac68-ee84c63eefd7
-- title:
--   C6 Bipartite Domination: paper10 fiber plus one le degree
-- statement:
--   For every `z ∈ Z₀`, its special vertices together with one additional
--   `S`-neighbor fit in the `S`-neighborhood of `z`.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L121-L214
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection10.lean#L121-L214

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper10_fiber_plus_one_le_degree
    {D Q : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G)
    (hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q) {z : V}
    (hz : z ∈ Z0Part G D) :
    (paper10SpecialFiber G hCan hmax Q hQ z).card + 1 ≤ degreeTo G (SPart G D) z := by sorry
