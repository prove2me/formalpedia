-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_Z1Part
-- name    : C6BipartiteDomination.mem_Z1Part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:49.630003+00:00
-- url     : https://prove2.me/theorems/5fb03e01-2fe3-479a-abce-98da976d41f1
-- title:
--   C6 Bipartite Domination: mem Z1 Part
-- statement:
--   The C6 Bipartite Domination construction uses the mem Z1 Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L61-L65
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L61-L65

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_Z1Part (D : Finset V) (z : V) :
    z ∈ Z1Part G D ↔
      z ∈ ZPart G D ∧ ∃ w ∈ W0Part G D, G.Adj z w := by sorry
