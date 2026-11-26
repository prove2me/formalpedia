-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_sharedCompensation
-- name    : C6BipartiteDomination.mem_sharedCompensation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:48:54.463049+00:00
-- url     : https://prove2.me/theorems/dd1ab084-2caa-59f4-9e00-64b4e6264dc6
-- title:
--   C6 Bipartite Domination: mem shared Compensation
-- statement:
--   The C6 Bipartite Domination construction uses the mem shared Compensation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L76-L80
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L76-L80

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_sharedCompensation (D X : Finset V) (u q : V) :
    q ∈ sharedCompensation G D X u ↔
      q ∉ D ∧ ∃ z ∈ X, neighborhoodIn G D q = {u, z} := by sorry
