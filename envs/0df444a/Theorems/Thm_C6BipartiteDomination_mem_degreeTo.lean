-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_degreeTo
-- name    : C6BipartiteDomination.mem_degreeTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:39.760188+00:00
-- url     : https://prove2.me/theorems/6dc56cd6-d0c6-4377-a8dd-7ceb15e8cb9c
-- title:
--   C6 Bipartite Domination: mem degree To
-- statement:
--   The C6 Bipartite Domination construction uses the mem degree To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L32-L34
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L32-L34

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
open Classical

theorem C6BipartiteDomination.mem_degreeTo (A : Finset V) (v u : V) :
    u ∈ A.filter (fun x => G.Adj v x) ↔ u ∈ A ∧ G.Adj v u := by sorry
