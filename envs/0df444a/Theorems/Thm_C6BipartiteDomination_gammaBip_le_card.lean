-- Prove2me | Theorems.Thm_C6BipartiteDomination_gammaBip_le_card
-- name    : C6BipartiteDomination.gammaBip_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:01.596902+00:00
-- url     : https://prove2.me/theorems/bd090204-11bf-4c51-bea9-19852ec3d410
-- title:
--   C6 Bipartite Domination: gamma Bip le card
-- statement:
--   The C6 Bipartite Domination construction uses the gamma Bip le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L277-L281
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/ExtremalResults.lean#L277-L281

import Definitions.Def_C6BipartiteDomination_MainResults
import Definitions.Def_C6BipartiteDomination_Corona
import Definitions.Def_C6BipartiteDomination_ExtremalResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem C6BipartiteDomination.gammaBip_le_card (G : SimpleGraph V) {D : Finset V}
    (hD : IsBipartiteDominatingSet G D) :
    gammaBip G ≤ D.card := by sorry
