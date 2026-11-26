-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_3_1_private_neighbors
-- name    : C6BipartiteDomination.lemma_3_1_private_neighbors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:05.437418+00:00
-- url     : https://prove2.me/theorems/c1e23303-7471-5ab4-8984-2b2f248a286d
-- title:
--   C6 Bipartite Domination: lemma 3 1 private neighbors
-- statement:
--   Lemma 3.1: every selected vertex that is non-isolated in the induced
--   selected graph has at least two external private neighbors.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L277-L292
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A4.lean#L277-L292

import Definitions.Def_C6BipartiteDomination_A3
import Definitions.Def_C6BipartiteDomination_A4
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_3_1_private_neighbors
    {D : Finset V} {b : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hb : NonisolatedIn G D b) :
    2 ≤ (privateExternalNeighbors G D b).card := by sorry
