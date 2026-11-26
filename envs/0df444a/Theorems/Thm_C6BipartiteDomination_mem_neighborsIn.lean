-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_neighborsIn
-- name    : C6BipartiteDomination.mem_neighborsIn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:14.825309+00:00
-- url     : https://prove2.me/theorems/3c951066-d89b-40e4-9408-dafadead24b0
-- title:
--   C6 Bipartite Domination: mem neighbors In
-- statement:
--   The C6 Bipartite Domination construction uses the mem neighbors In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L35-L38
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L35-L38

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_neighborsIn (S T : Finset V) (w : V) :
    w ∈ neighborsIn G S T ↔ w ∈ T ∧ ∃ v ∈ S, G.Adj v w := by sorry
