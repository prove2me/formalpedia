-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_projectFinsetFromSubtype
-- name    : C6BipartiteDomination.mem_projectFinsetFromSubtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:20.861127+00:00
-- url     : https://prove2.me/theorems/b40f5016-9870-48b1-8e2b-6d8f574f41c5
-- title:
--   C6 Bipartite Domination: mem project Finset From Subtype
-- statement:
--   The C6 Bipartite Domination construction uses the mem project Finset From Subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L59-L64
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L59-L64

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_projectFinsetFromSubtype {S : Finset V}
    (F : Finset {v // v ∈ S}) (v : V) :
    v ∈ projectFinsetFromSubtype (S := S) F ↔
      ∃ x ∈ F, x.1 = v := by sorry
