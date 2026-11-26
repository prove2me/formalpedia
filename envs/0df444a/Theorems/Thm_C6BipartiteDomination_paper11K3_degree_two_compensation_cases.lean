-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_degree_two_compensation_cases
-- name    : C6BipartiteDomination.paper11K3_degree_two_compensation_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:33.984831+00:00
-- url     : https://prove2.me/theorems/31d44249-cd87-47c2-8b6b-691afa752981
-- title:
--   C6 Bipartite Domination: paper11 K3 degree two compensation cases
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 degree two compensation cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L658-L741
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L658-L741

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_degree_two_compensation_cases {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax)
    (hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 2) :
    (xCharge G D u = 1 ∧ vertexCharge G D u = 11 ∧
      paper11K3Compensation G D hCan hmax u = ∅) ∨
    (xCharge G D u = 0 ∧ vertexCharge G D u = 0 ∧
      ∃ q, paper11K3Compensation G D hCan hmax u = {q} ∧
        externalCharge G D q = 4 ∧
        q ∈ paper10SpecialQSet G hCan hmax ∧
        ∃ data : Paper10SpecialWitness G hCan hmax q, data.u = u) := by sorry
