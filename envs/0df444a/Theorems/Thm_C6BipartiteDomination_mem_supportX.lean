-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_supportX
-- name    : C6BipartiteDomination.mem_supportX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:36.076983+00:00
-- url     : https://prove2.me/theorems/22daba26-82ea-4190-a52e-7b5b3a6e010d
-- title:
--   C6 Bipartite Domination: mem support X
-- statement:
--   The C6 Bipartite Domination construction uses the mem support X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L27-L30
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L27-L30

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_supportX (D : Finset V) (w z : V) :
    z ∈ supportX G D w ↔ z ∈ Z0Part G D ∧ G.Adj w z := by sorry
