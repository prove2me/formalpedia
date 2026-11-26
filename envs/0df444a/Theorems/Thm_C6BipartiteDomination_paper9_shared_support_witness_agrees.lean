-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_shared_support_witness_agrees
-- name    : C6BipartiteDomination.paper9_shared_support_witness_agrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:12.843372+00:00
-- url     : https://prove2.me/theorems/e765cb6e-b7bd-4ba8-9fa8-8e15bec43802
-- title:
--   C6 Bipartite Domination: paper9 shared support witness agrees
-- statement:
--   The isolated support vertex in a shared-compensation description is
--   unique, even when the same compensation vertex is shared by two supports.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L445-L471
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L445-L471

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_shared_support_witness_agrees
    {D X Y : Finset V} {u q : V}
    (huB : u ∈ BPart G D)
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (hqX : q ∈ sharedCompensation G D X u)
    (hqY : q ∈ sharedCompensation G D Y u) :
    ∃ z, z ∈ X ∧ z ∈ Y ∧ neighborhoodIn G D q = {u, z} := by sorry
