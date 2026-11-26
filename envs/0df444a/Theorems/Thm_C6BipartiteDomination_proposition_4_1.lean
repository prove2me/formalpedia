-- Prove2me | Theorems.Thm_C6BipartiteDomination_proposition_4_1
-- name    : C6BipartiteDomination.proposition_4_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:42:41.894379+00:00
-- url     : https://prove2.me/theorems/32c4ffca-3f88-41ca-b26f-9e1f81c121e3
-- title:
--   C6 Bipartite Domination: proposition 4 1
-- statement:
--   Proposition 4.1 (the local Hall-deficiency step). The no-isolated-vertices
--   hypothesis is the ambient assumption of the paper; it ensures every selected
--   vertex has an external neighbor.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L260-L367
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L260-L367

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.proposition_4_1
    {D : Finset V}
    (hD : IsBipartiteDominatingSet G D)
    (hmin : ∀ E, IsBipartiteDominatingSet G E → D.card ≤ E.card)
    (hDind : Independent G D)
    (hNoIso : HasNoIsolatedVertices G) :
    D.card ≤ (Finset.univ \ D).card := by sorry
