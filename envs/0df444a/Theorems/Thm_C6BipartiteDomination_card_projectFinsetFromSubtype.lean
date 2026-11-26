-- Prove2me | Theorems.Thm_C6BipartiteDomination_card_projectFinsetFromSubtype
-- name    : C6BipartiteDomination.card_projectFinsetFromSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:13.834635+00:00
-- url     : https://prove2.me/theorems/abde79cb-c198-47a4-8b3d-f2348d052a40
-- title:
--   C6 Bipartite Domination: card project Finset From Subtype
-- statement:
--   The C6 Bipartite Domination construction uses the card project Finset From Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L66-L74
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L66-L74

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.card_projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) :
    (projectFinsetFromSubtype (S := S) F).card = F.card := by sorry
