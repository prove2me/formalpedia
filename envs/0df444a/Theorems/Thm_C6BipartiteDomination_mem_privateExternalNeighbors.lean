-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors
-- name    : C6BipartiteDomination.mem_privateExternalNeighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:42:11.381932+00:00
-- url     : https://prove2.me/theorems/a8c68fde-cf14-5025-9a9d-db66138b0f1f
-- title:
--   C6 Bipartite Domination: mem private External Neighbors
-- statement:
--   The C6 Bipartite Domination construction uses the mem private External Neighbors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L86-L90
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L86-L90

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_privateExternalNeighbors (D : Finset V) (b w : V) :
    w ∈ privateExternalNeighbors G D b ↔
      w ∉ D ∧ ∀ u ∈ D, G.Adj u w ↔ u = b := by sorry
