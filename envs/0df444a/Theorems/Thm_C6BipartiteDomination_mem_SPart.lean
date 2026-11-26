-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_SPart
-- name    : C6BipartiteDomination.mem_SPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:37.329403+00:00
-- url     : https://prove2.me/theorems/3867fe81-9320-4f57-acc8-31714cfd16e5
-- title:
--   C6 Bipartite Domination: mem SPart
-- statement:
--   The C6 Bipartite Domination construction uses the mem SPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L58-L60
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L58-L60

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_SPart (D : Finset V) (w : V) :
    w ∈ SPart G D ↔ w ∈ WBPart G D ∧ w ∉ PPart G D := by sorry
