-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_core_vertices_subset
-- name    : C6BipartiteDomination.corona_core_vertices_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:38.519564+00:00
-- url     : https://prove2.me/theorems/b3f2fce4-4277-45a2-9b2c-637cee2073ed
-- title:
--   C6 Bipartite Domination: corona core vertices subset
-- statement:
--   The C6 Bipartite Domination construction uses the corona core vertices subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L208-L212
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L208-L212

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_core_vertices_subset {D : Finset CoronaVertex} :
    coronaSelectedCoreVertices D ⊆ D := by sorry
