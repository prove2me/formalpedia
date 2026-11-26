-- Prove2me | Theorems.Thm_C6BipartiteDomination_responsible_iff
-- name    : C6BipartiteDomination.responsible_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:39:53.692269+00:00
-- url     : https://prove2.me/theorems/b4a157ff-e57e-5cf6-8584-9cd3b720605c
-- title:
--   C6 Bipartite Domination: responsible iff
-- statement:
--   The responsibility region can be expressed directly through absence of
--   neighbors in the retained set.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Basic.lean#L67-L69
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/Basic.lean#L67-L69

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Tactic
import Definitions.Def_C6BipartiteDomination_Basic
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.responsible_iff
    (D X : Finset V) (v : V) :
    Responsible G D X v ↔ v ∉ D \ X ∧ ∀ u ∈ D \ X, ¬ G.Adj u v := by sorry
