-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_forced_leaves_card
-- name    : C6BipartiteDomination.corona_forced_leaves_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:02.668073+00:00
-- url     : https://prove2.me/theorems/8adab37f-eb77-497c-b87f-7545f116b2fa
-- title:
--   C6 Bipartite Domination: corona forced leaves card
-- statement:
--   The C6 Bipartite Domination construction uses the corona forced leaves card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L189-L197
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L189-L197

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_forced_leaves_card (D : Finset CoronaVertex) :
    (coronaForcedLeaves D).card =
      (coronaUnselectedCore D).card * 2 := by sorry
