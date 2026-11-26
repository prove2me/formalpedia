-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper9_lemma_9_2
-- name    : C6BipartiteDomination.paper9_lemma_9_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:10.256904+00:00
-- url     : https://prove2.me/theorems/46290c81-2695-553c-811a-e18eb5cf81c0
-- title:
--   C6 Bipartite Domination: paper9 lemma 9 2
-- statement:
--   Paper Lemma 9.2 for a degree-two vertex in the chosen repair graph. The
--   two alternatives record the exact compensation sets, charges, and shared
--   support point from cases (a) and (b).
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L619-L800
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection9.lean#L619-L800

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper9_lemma_9_2
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hTcard : T.card = 2) :
    (∀ w ∈ T, kCharge G D w = 3) ∧
      ((xCharge G D u = 1 ∧ sCharge G D u = 2 ∧
          vertexCharge G D u = 11 ∧
          ∀ w ∈ T, sharedCompensation G D (supportX G D w) u = ∅) ∨
       (xCharge G D u = 0 ∧ sCharge G D u = 3 ∧
          vertexCharge G D u = 0 ∧
          ∃ q z, (∀ w ∈ T,
              sharedCompensation G D (supportX G D w) u = {q}) ∧
            q ∈ SPart G D ∧ betaCharge G D q = 1 ∧
            kCharge G D q = 1 ∧ externalCharge G D q = 4 ∧
            z ∈ Z0Part G D ∧ neighborhoodIn G D q = {u, z} ∧
            ∀ w ∈ T, z ∈ supportX G D w)) := by sorry
