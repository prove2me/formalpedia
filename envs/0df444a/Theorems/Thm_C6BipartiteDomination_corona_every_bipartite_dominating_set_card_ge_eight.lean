-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_every_bipartite_dominating_set_card_ge_eight
-- name    : C6BipartiteDomination.corona_every_bipartite_dominating_set_card_ge_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:15.573065+00:00
-- url     : https://prove2.me/theorems/b619457b-8e49-50a0-a3d2-b623754767b9
-- title:
--   C6 Bipartite Domination: corona every bipartite dominating set card ge eight
-- statement:
--   The C6 Bipartite Domination construction uses the corona every bipartite dominating set card ge eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L223-L243
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L223-L243

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_every_bipartite_dominating_set_card_ge_eight
    {D : Finset CoronaVertex} (hD : IsBipartiteDominatingSet coronaGraph D) :
    8 ≤ D.card := by sorry
