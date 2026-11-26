-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_Z0Part
-- name    : C6BipartiteDomination.mem_Z0Part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:31.607335+00:00
-- url     : https://prove2.me/theorems/24a07295-9d18-460b-b689-03ffdba16aa7
-- title:
--   C6 Bipartite Domination: mem Z0 Part
-- statement:
--   The C6 Bipartite Domination construction uses the mem Z0 Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L56-L59
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L56-L59

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_Z0Part (D : Finset V) (z : V) :
    z ∈ Z0Part G D ↔ z ∈ ZPart G D ∧ ∀ w ∈ W0Part G D, ¬ G.Adj z w := by sorry
