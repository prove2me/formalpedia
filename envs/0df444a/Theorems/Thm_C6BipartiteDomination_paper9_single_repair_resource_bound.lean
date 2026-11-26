-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_single_repair_resource_bound
-- name    : C6BipartiteDomination.paper9_single_repair_resource_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:54:07.589834+00:00
-- url     : https://prove2.me/theorems/81f769c0-6622-5c92-99b0-6af19638ab0e
-- title:
--   C6 Bipartite Domination: paper9 single repair resource bound
-- statement:
--   Paper Lemma 9.3's compensation estimate. The degree-one hypothesis is not
--   needed once a particular chosen repair edge is fixed: the local budget and
--   Lemma 8.5 already give the same bound for each such edge.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L330-L393
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L330-L393

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_single_repair_resource_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u w : V} (huB : u ∈ BPart G D) (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    (hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u)
    (hk : kCharge G D w = 3 ∨ kCharge G D w = 4) :
    (kCharge G D w = 3 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 4) ∨
    (kCharge G D w = 4 ∧
      vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ≥ 8) := by sorry
