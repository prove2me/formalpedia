-- Prove2me | Theorems.Thm_C6BipartiteDomination_supportB_card
-- name    : C6BipartiteDomination.supportB_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:00.863639+00:00
-- url     : https://prove2.me/theorems/9a0c3417-06e8-46c8-a24f-601c0420e3e8
-- title:
--   C6 Bipartite Domination: support B card
-- statement:
--   The C6 Bipartite Domination construction uses the support B card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L37-L39
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L37-L39

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.supportB_card (D : Finset V) (w : V) :
    (supportB G D w).card = betaCharge G D w := by sorry
