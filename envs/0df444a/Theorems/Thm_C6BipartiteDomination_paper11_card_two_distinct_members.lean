-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_card_two_distinct_members
-- name    : C6BipartiteDomination.paper11_card_two_distinct_members
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:03.878961+00:00
-- url     : https://prove2.me/theorems/f88f074b-0729-4154-bcd1-a77fda232c5a
-- title:
--   C6 Bipartite Domination: paper11 card two distinct members
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 card two distinct members property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L500-L511
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L500-L511

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_card_two_distinct_members {T : Finset V} (hT : T.card = 2) :
    ∃ a b, a ≠ b ∧ a ∈ T ∧ b ∈ T := by sorry
