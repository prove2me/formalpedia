-- Prove2me | Theorems.Thm_C6BipartiteDomination_privateExternal_pairwiseDisjoint
-- name    : C6BipartiteDomination.privateExternal_pairwiseDisjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:37.631413+00:00
-- url     : https://prove2.me/theorems/0b661106-24d2-4843-a16e-75c0ec9c082d
-- title:
--   C6 Bipartite Domination: private External pairwise Disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the private External pairwise Disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L62-L76
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L62-L76

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.privateExternal_pairwiseDisjoint (D : Finset V) :
    (BPart G D : Set V).PairwiseDisjoint (privateExternalNeighbors G D) := by sorry
