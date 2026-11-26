-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_8_4_compensation_decomposition
-- name    : C6BipartiteDomination.lemma_8_4_compensation_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:15.926847+00:00
-- url     : https://prove2.me/theorems/49ac5ca6-7c5c-54c0-8a4b-2744c65efd39
-- title:
--   C6 Bipartite Domination: lemma 8 4 compensation decomposition
-- statement:
--   The exact decomposition in Lemma 8.4.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L311-L465
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L311-L465

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_8_4_compensation_decomposition
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V}
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    let X := supportX G D w
    let Q := compensationRegion G D X u w
    Q = privateCompensation G D u ∪ sharedCompensation G D X u ∧
      Disjoint (privateCompensation G D u) (sharedCompensation G D X u) ∧
      ∀ q ∈ Q, q ∉ D ∧ G.Adj u q := by sorry
