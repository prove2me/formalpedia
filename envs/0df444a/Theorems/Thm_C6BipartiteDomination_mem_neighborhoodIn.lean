-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
-- name    : C6BipartiteDomination.mem_neighborhoodIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:43.41562+00:00
-- url     : https://prove2.me/theorems/82189f22-9985-4586-9577-9c405bf66528
-- title:
--   C6 Bipartite Domination: mem neighborhood In
-- statement:
--   The C6 Bipartite Domination construction uses the mem neighborhood In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L23-L26
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L23-L26

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_neighborhoodIn (D : Finset V) (q d : V) :
    d ∈ neighborhoodIn G D q ↔ d ∈ D ∧ G.Adj q d := by sorry
