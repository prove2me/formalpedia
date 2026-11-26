-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_selected_core_vertices_card
-- name    : C6BipartiteDomination.corona_selected_core_vertices_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:53.567371+00:00
-- url     : https://prove2.me/theorems/e6f04c4d-3951-4b98-b475-1b202024d7af
-- title:
--   C6 Bipartite Domination: corona selected core vertices card
-- statement:
--   The C6 Bipartite Domination construction uses the corona selected core vertices card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L181-L187
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L181-L187

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_selected_core_vertices_card (D : Finset CoronaVertex) :
    (coronaSelectedCoreVertices D).card = (coronaSelectedCore D).card := by sorry
