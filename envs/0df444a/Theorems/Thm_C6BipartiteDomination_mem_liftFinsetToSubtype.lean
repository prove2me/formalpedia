-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_liftFinsetToSubtype
-- name    : C6BipartiteDomination.mem_liftFinsetToSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:42.493814+00:00
-- url     : https://prove2.me/theorems/98a1124c-786b-5638-a2c9-a477fc26261c
-- title:
--   C6 Bipartite Domination: mem lift Finset To Subtype
-- statement:
--   The C6 Bipartite Domination construction uses the mem lift Finset To Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L28-L40
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L28-L40

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_liftFinsetToSubtype {S E : Finset V} (hES : E ⊆ S)
    (x : {v // v ∈ S}) :
    x ∈ liftFinsetToSubtype S E hES ↔ x.1 ∈ E := by sorry
