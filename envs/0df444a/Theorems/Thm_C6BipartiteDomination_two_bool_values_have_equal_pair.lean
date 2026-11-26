-- Prove2me | Theorems.Thm_C6BipartiteDomination_two_bool_values_have_equal_pair
-- name    : C6BipartiteDomination.two_bool_values_have_equal_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:34.545639+00:00
-- url     : https://prove2.me/theorems/07ae718f-5dcd-5719-9521-4197c999e03e
-- title:
--   C6 Bipartite Domination: two bool values have equal pair
-- statement:
--   The C6 Bipartite Domination construction uses the two bool values have equal pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L180-L182
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L180-L182

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.two_bool_values_have_equal_pair (a b d : Bool) :
    a = b ∨ a = d ∨ b = d := by sorry
