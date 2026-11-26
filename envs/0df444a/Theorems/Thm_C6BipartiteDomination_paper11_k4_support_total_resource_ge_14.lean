-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_k4_support_total_resource_ge_14
-- name    : C6BipartiteDomination.paper11_k4_support_total_resource_ge_14
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:41.25651+00:00
-- url     : https://prove2.me/theorems/019be631-b800-4188-9496-cece1f0d3d8f
-- title:
--   C6 Bipartite Domination: paper11 k4 support total resource ge 14
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 k4 support total resource ge 14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L631-L652
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L631-L652

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_k4_support_total_resource_ge_14 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      16 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) ∧
      14 ≤
        (vertexCharge G D u +
          ∑ q ∈ sharedCompensation G D (supportX G D w) u,
            externalCharge G D q) +
        (vertexCharge G D v +
          ∑ q ∈ sharedCompensation G D (supportX G D w) v,
            externalCharge G D q) := by sorry
