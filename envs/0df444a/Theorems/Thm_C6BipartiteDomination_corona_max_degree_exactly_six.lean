-- Prove2me | Theorems.Thm_C6BipartiteDomination_corona_max_degree_exactly_six
-- name    : C6BipartiteDomination.corona_max_degree_exactly_six
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:09:23.92614+00:00
-- url     : https://prove2.me/theorems/6e6e1b80-feb2-5b3c-a7bd-ac477eef170a
-- title:
--   C6 Bipartite Domination: corona max degree exactly six
-- statement:
--   The C6 Bipartite Domination construction uses the corona max degree exactly six property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L101-L104
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L101-L104

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical

theorem C6BipartiteDomination.corona_max_degree_exactly_six :
    (∀ v, degreeTo coronaGraph Finset.univ v ≤ 6) ∧
      (∃ v, degreeTo coronaGraph Finset.univ v = 6) := by sorry
