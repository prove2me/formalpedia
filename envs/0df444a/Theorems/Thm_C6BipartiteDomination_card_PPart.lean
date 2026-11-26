-- Prove2me | Theorems.Thm_C6BipartiteDomination_card_PPart
-- name    : C6BipartiteDomination.card_PPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:48.380722+00:00
-- url     : https://prove2.me/theorems/713ce9c5-4c5a-48a6-b095-3a7219cd1112
-- title:
--   C6 Bipartite Domination: card PPart
-- statement:
--   The C6 Bipartite Domination construction uses the card PPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L90-L94
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L90-L94

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.card_PPart (D : Finset V) :
    (PPart G D).card = ∑ b ∈ BPart G D, (privateExternalNeighbors G D b).card := by sorry
