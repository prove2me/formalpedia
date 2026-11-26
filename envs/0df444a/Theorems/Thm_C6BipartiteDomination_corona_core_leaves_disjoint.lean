-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_core_leaves_disjoint
-- name    : C6BipartiteDomination.corona_core_leaves_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:58.342682+00:00
-- url     : https://prove2.me/theorems/769d7909-e559-53fb-9a82-79a7a3d5770a
-- title:
--   C6 Bipartite Domination: corona core leaves disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the corona core leaves disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L199-L206
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L199-L206

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_core_leaves_disjoint (D : Finset CoronaVertex) :
    Disjoint (coronaSelectedCoreVertices D) (coronaForcedLeaves D) := by sorry
