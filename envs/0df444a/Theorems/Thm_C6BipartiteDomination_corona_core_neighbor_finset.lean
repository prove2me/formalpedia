-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_core_neighbor_finset
-- name    : C6BipartiteDomination.corona_core_neighbor_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:32.526204+00:00
-- url     : https://prove2.me/theorems/e22a5cd7-40d2-5c3d-ad3c-8765dc2d9dbe
-- title:
--   C6 Bipartite Domination: corona core neighbor finset
-- statement:
--   The C6 Bipartite Domination construction uses the corona core neighbor finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L17-L32
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L17-L32

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_core_neighbor_finset (i : Fin 5) :
    Finset.univ.filter (fun u => coronaGraph.Adj (Sum.inl i) u) =
      (Finset.univ.erase i).image (fun j : Fin 5 => (Sum.inl j : CoronaVertex)) ∪
        ({Sum.inr (i, 0), Sum.inr (i, 1)} : Finset CoronaVertex) := by sorry
