-- Prove2me | Theorems.Thm_C6BipartiteDomination_card_liftFinsetToSubtype
-- name    : C6BipartiteDomination.card_liftFinsetToSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:14.364134+00:00
-- url     : https://prove2.me/theorems/1bd7bb43-6aa9-588a-9041-9791b7f40d25
-- title:
--   C6 Bipartite Domination: card lift Finset To Subtype
-- statement:
--   The C6 Bipartite Domination construction uses the card lift Finset To Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L42-L52
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L42-L52

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.card_liftFinsetToSubtype {S E : Finset V} (hES : E ⊆ S) :
    (liftFinsetToSubtype S E hES).card = E.card := by sorry
