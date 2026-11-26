-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_privateCompensation
-- name    : C6BipartiteDomination.mem_privateCompensation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:07.637426+00:00
-- url     : https://prove2.me/theorems/961af5a7-ab3a-445a-b638-7864f004f7e0
-- title:
--   C6 Bipartite Domination: mem private Compensation
-- statement:
--   The C6 Bipartite Domination construction uses the mem private Compensation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L43-L74
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L43-L74

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_privateCompensation (D : Finset V) (u q : V) :
    u ∈ D → (q ∈ privateCompensation G D u ↔
      q ∉ D ∧ neighborhoodIn G D q = {u}) := by sorry
