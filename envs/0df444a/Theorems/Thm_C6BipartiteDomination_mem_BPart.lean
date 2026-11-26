-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_BPart
-- name    : C6BipartiteDomination.mem_BPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:37.480725+00:00
-- url     : https://prove2.me/theorems/783efeef-b561-49ed-a927-ade70749ddf7
-- title:
--   C6 Bipartite Domination: mem BPart
-- statement:
--   The C6 Bipartite Domination construction uses the mem BPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L47-L49
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L47-L49

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_BPart (D : Finset V) (b : V) :
    b ∈ BPart G D ↔ b ∈ D ∧ b ∉ ZPart G D := by sorry
