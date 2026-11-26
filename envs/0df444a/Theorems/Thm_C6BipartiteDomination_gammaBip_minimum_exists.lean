-- Prove2me | Theorems.Thm_C6BipartiteDomination_gammaBip_minimum_exists
-- name    : C6BipartiteDomination.gammaBip_minimum_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:21.550916+00:00
-- url     : https://prove2.me/theorems/1a39c5c3-8130-4ca8-9b7c-70c409581a6a
-- title:
--   C6 Bipartite Domination: gamma Bip minimum exists
-- statement:
--   The C6 Bipartite Domination construction uses the gamma Bip minimum exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L283-L290
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L283-L290

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem C6BipartiteDomination.gammaBip_minimum_exists (G : SimpleGraph V) :
    ∃ D : Finset V,
      MinimumBipartiteDominatingSet G D ∧ D.card = gammaBip G := by sorry
