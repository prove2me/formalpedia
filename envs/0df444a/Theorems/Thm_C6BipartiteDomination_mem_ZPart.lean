-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_ZPart
-- name    : C6BipartiteDomination.mem_ZPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:19.536358+00:00
-- url     : https://prove2.me/theorems/5208967f-8eee-55a5-a2b4-bd3b3c743fe9
-- title:
--   C6 Bipartite Domination: mem ZPart
-- statement:
--   The C6 Bipartite Domination construction uses the mem ZPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L42-L45
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L42-L45

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_ZPart (D : Finset V) (z : V) :
    z ∈ ZPart G D ↔ z ∈ D ∧ ∀ u ∈ D, ¬ G.Adj z u := by sorry
