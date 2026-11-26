-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_vertex_card
-- name    : C6BipartiteDomination.corona_vertex_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:44.303801+00:00
-- url     : https://prove2.me/theorems/154e37d8-15b6-5813-9f76-e3fc69b3d371
-- title:
--   C6 Bipartite Domination: corona vertex card
-- statement:
--   The C6 Bipartite Domination construction uses the corona vertex card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L106-L107
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L106-L107

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_vertex_card : Fintype.card CoronaVertex = 15 := by sorry
