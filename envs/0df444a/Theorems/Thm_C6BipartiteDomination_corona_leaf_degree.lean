-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_leaf_degree
-- name    : C6BipartiteDomination.corona_leaf_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:49.121809+00:00
-- url     : https://prove2.me/theorems/011f1a08-c28f-5cb9-a328-e4b76adcdafd
-- title:
--   C6 Bipartite Domination: corona leaf degree
-- statement:
--   The C6 Bipartite Domination construction uses the corona leaf degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L70-L75
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L70-L75

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_leaf_degree (i : Fin 5) (p : Fin 2) :
    degreeTo coronaGraph Finset.univ (Sum.inr (i, p)) = 1 := by sorry
