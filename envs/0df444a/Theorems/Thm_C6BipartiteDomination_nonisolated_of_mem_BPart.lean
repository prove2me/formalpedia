-- Prove2me | Theorems.Thm_C6BipartiteDomination_nonisolated_of_mem_BPart
-- name    : C6BipartiteDomination.nonisolated_of_mem_BPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:33.696152+00:00
-- url     : https://prove2.me/theorems/59f379c8-6e06-4808-b661-d0a97d99ae09
-- title:
--   C6 Bipartite Domination: nonisolated of mem BPart
-- statement:
--   The C6 Bipartite Domination construction uses the nonisolated of mem BPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L118-L128
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L118-L128

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.nonisolated_of_mem_BPart {D : Finset V} {b : V}
    (hb : b ∈ BPart G D) : NonisolatedIn G D b := by sorry
