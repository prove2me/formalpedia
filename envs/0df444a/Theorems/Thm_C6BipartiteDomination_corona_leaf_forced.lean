-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_leaf_forced
-- name    : C6BipartiteDomination.corona_leaf_forced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:48.684138+00:00
-- url     : https://prove2.me/theorems/bbb148f1-2b4b-590c-b796-f58972f6f738
-- title:
--   C6 Bipartite Domination: corona leaf forced
-- statement:
--   The C6 Bipartite Domination construction uses the corona leaf forced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L152-L169
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L152-L169

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_leaf_forced {D : Finset CoronaVertex}
    (hD : IsBipartiteDominatingSet coronaGraph D)
    {i : Fin 5} (hi : i ∉ coronaSelectedCore D) (p : Fin 2) :
    Sum.inr (i, p) ∈ D := by sorry
