-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_PPart
-- name    : C6BipartiteDomination.mem_PPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:01.953592+00:00
-- url     : https://prove2.me/theorems/54fc3107-ea83-5b7a-b7c5-d12bd2fd3bc8
-- title:
--   C6 Bipartite Domination: mem PPart
-- statement:
--   The C6 Bipartite Domination construction uses the mem PPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L53-L56
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L53-L56

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_PPart (D : Finset V) (w : V) :
    w ∈ PPart G D ↔ ∃ b ∈ BPart G D, w ∈ privateExternalNeighbors G D b := by sorry
