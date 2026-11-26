-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_selected_core_card_le_two
-- name    : C6BipartiteDomination.corona_selected_core_card_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:52.398731+00:00
-- url     : https://prove2.me/theorems/f21b3b98-9ac2-5e9f-9649-a6e4b3e5d136
-- title:
--   C6 Bipartite Domination: corona selected core card le two
-- statement:
--   The C6 Bipartite Domination construction uses the corona selected core card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L124-L150
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L124-L150

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_selected_core_card_le_two {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    (coronaSelectedCore D).card ≤ 2 := by sorry
