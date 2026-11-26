-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_leaf_neighbor_finset
-- name    : C6BipartiteDomination.corona_leaf_neighbor_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:55.585819+00:00
-- url     : https://prove2.me/theorems/15951abe-770e-41ba-96a3-2ae1e859cd07
-- title:
--   C6 Bipartite Domination: corona leaf neighbor finset
-- statement:
--   The C6 Bipartite Domination construction uses the corona leaf neighbor finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L34-L45
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L34-L45

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_leaf_neighbor_finset (i : Fin 5) (p : Fin 2) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inr (i, p)) u) =
      {Sum.inl i} := by sorry
