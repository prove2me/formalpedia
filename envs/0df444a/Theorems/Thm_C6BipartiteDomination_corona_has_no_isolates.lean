-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_has_no_isolates
-- name    : C6BipartiteDomination.corona_has_no_isolates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:49.098058+00:00
-- url     : https://prove2.me/theorems/1ad6bf89-1fa6-4bdb-9416-96256601d92c
-- title:
--   C6 Bipartite Domination: corona has no isolates
-- statement:
--   The C6 Bipartite Domination construction uses the corona has no isolates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L77-L87
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L77-L87

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_has_no_isolates : HasNoIsolatedVertices coronaGraph := by sorry
