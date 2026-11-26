-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_internalArcs
-- name    : C6BipartiteDomination.mem_internalArcs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:42:15.352931+00:00
-- url     : https://prove2.me/theorems/c6844ea4-bbe1-5eb1-8ac9-cd343ff3afcd
-- title:
--   C6 Bipartite Domination: mem internal Arcs
-- statement:
--   The C6 Bipartite Domination construction uses the mem internal Arcs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L24-L27
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L24-L27

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_internalArcs (D : Finset V) (u v : V) :
    (u, v) ∈ internalArcs G D ↔ u ∈ D ∧ v ∈ D ∧ G.Adj u v := by sorry
