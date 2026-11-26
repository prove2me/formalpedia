-- Prove2me | Theorems.Thm_C6BipartiteDomination_neighborsIn_eq_of_dominates
-- name    : C6BipartiteDomination.neighborsIn_eq_of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:19.518382+00:00
-- url     : https://prove2.me/theorems/af68900c-13b0-54ea-b51d-27d964ab56bc
-- title:
--   C6 Bipartite Domination: neighbors In eq of dominates
-- statement:
--   The C6 Bipartite Domination construction uses the neighbors In eq of dominates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L77-L89
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L77-L89

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.neighborsIn_eq_of_dominates
    {D W : Finset V}
    (hdom : ∀ ⦃w⦄, w ∈ W → ∃ d ∈ D, G.Adj d w) :
    neighborsIn G D W = W := by sorry
