-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_shared_beta_eq_one
-- name    : C6BipartiteDomination.paper9_shared_beta_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:34.346614+00:00
-- url     : https://prove2.me/theorems/0816f761-e29c-4177-9094-e06b15df7a07
-- title:
--   C6 Bipartite Domination: paper9 shared beta eq one
-- statement:
--   A shared compensation vertex has exactly one neighbor in `B`, namely its
--   repair vertex.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L272-L312
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L272-L312

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_shared_beta_eq_one
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    betaCharge G D q = 1 := by sorry
