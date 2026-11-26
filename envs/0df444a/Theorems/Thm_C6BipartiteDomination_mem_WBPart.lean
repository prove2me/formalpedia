-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_WBPart
-- name    : C6BipartiteDomination.mem_WBPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:44:59.492046+00:00
-- url     : https://prove2.me/theorems/7d36a68b-8385-50f3-913e-da794eb2c43e
-- title:
--   C6 Bipartite Domination: mem WBPart
-- statement:
--   The C6 Bipartite Domination construction uses the mem WBPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L49-L51
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L49-L51

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_WBPart (D : Finset V) (w : V) :
    w ∈ WBPart G D ↔ w ∉ D ∧ w ∉ W0Part G D := by sorry
