-- Prove2me | Theorems.Thm_C6BipartiteDomination_lemma_8_5_independent_set_lower_bound
-- name    : C6BipartiteDomination.lemma_8_5_independent_set_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:18.285428+00:00
-- url     : https://prove2.me/theorems/64fc5fbd-1da7-54ec-8160-d26da41900a7
-- title:
--   C6 Bipartite Domination: lemma 8 5 independent set lower bound
-- statement:
--   Lemma 8.5: the induced compensation graph has an independent set of size
--   at least the support size. The proof builds the paper's replacement set and
--   uses only the explicitly chosen repair pair.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L503-L759
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L503-L759

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.lemma_8_5_independent_set_lower_bound
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0)
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    ∃ J : Finset V,
      J ⊆ compensationRegion G D (supportX G D w) u w ∧
      Independent G J ∧ kCharge G D w ≤ J.card := by sorry
