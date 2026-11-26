-- Prove2me | Theorems.Thm_C6BipartiteDomination_private_card_eq_two_add_x
-- name    : C6BipartiteDomination.private_card_eq_two_add_x
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:31.090871+00:00
-- url     : https://prove2.me/theorems/948892d0-5356-5211-a4ec-c2768a8ffe44
-- title:
--   C6 Bipartite Domination: private card eq two add x
-- statement:
--   The C6 Bipartite Domination construction uses the private card eq two add x property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L130-L137
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L130-L137

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.private_card_eq_two_add_x {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D) {b : V}
    (hb : b ∈ BPart G D) :
    (privateExternalNeighbors G D b).card = 2 + xCharge G D b := by sorry
