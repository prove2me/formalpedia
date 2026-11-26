-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_forced_leaves_subset
-- name    : C6BipartiteDomination.corona_forced_leaves_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:15.753501+00:00
-- url     : https://prove2.me/theorems/ea84a3bc-dd71-5dd8-a65a-06e054ffac7f
-- title:
--   C6 Bipartite Domination: corona forced leaves subset
-- statement:
--   The C6 Bipartite Domination construction uses the corona forced leaves subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L214-L221
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L214-L221

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_forced_leaves_subset {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D) :
    coronaForcedLeaves D ⊆ D := by sorry
