-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_core_unselected_card
-- name    : C6BipartiteDomination.corona_core_unselected_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:59.926344+00:00
-- url     : https://prove2.me/theorems/802c52b5-38f9-4f6e-bd53-a1306f586804
-- title:
--   C6 Bipartite Domination: corona core unselected card
-- statement:
--   The C6 Bipartite Domination construction uses the corona core unselected card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L171-L179
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L171-L179

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_core_unselected_card {D : Finset CoronaVertex} :
    (coronaSelectedCore D).card + (coronaUnselectedCore D).card = 5 := by sorry
