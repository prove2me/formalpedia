-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_8_5_compensation_lower_bound
-- name    : C6BipartiteDomination.lemma_8_5_compensation_lower_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:49:29.015018+00:00
-- url     : https://prove2.me/theorems/89d7ab6e-0524-597c-bbc6-a1206301f44f
-- title:
--   C6 Bipartite Domination: lemma 8 5 compensation lower bound
-- statement:
--   The numerical compensation bound (12): the private surplus at `u` and
--   the shared compensation vertices together pay for the support size beyond
--   the two private neighbors.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L764-L790
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L764-L790

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_8_5_compensation_lower_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    kCharge G D w - 2 ≤
      xCharge G D u + (sharedCompensation G D (supportX G D w) u).card := by sorry
