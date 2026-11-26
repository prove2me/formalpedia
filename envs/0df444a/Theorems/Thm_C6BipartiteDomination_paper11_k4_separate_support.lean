-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_k4_separate_support
-- name    : C6BipartiteDomination.paper11_k4_separate_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:56.395744+00:00
-- url     : https://prove2.me/theorems/94038f43-0d3c-4bcb-843c-013a1c99766c
-- title:
--   C6 Bipartite Domination: paper11 k4 separate support
-- statement:
--   The `k=4` negative supports are accounted for separately. Each one has
--   two distinct chosen repair neighbors; Lemma 9.1 gives chosen degree one at
--   each neighbor, and Lemma 9.3 gives the two independent `8`-unit edge bounds.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L541-L629
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L541-L629

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_k4_separate_support {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      u ∈ paperChosenRepairSet G D hCan hmax w ∧
      v ∈ paperChosenRepairSet G D hCan hmax w ∧
      (paper11NegativeIncidentSupports G D hCan hmax u).card = 1 ∧
      (paper11NegativeIncidentSupports G D hCan hmax v).card = 1 ∧
      8 ≤ vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ∧
      8 ≤ vertexCharge G D v +
        ∑ q ∈ sharedCompensation G D (supportX G D w) v,
          externalCharge G D q := by sorry
