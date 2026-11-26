-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_eq_incident_card
-- name    : C6BipartiteDomination.paper11K3_right_degree_eq_incident_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:40.578031+00:00
-- url     : https://prove2.me/theorems/3b76a47f-4163-54f3-bd40-2c0154524531
-- title:
--   C6 Bipartite Domination: paper11 K3 right degree eq incident card
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 right degree eq incident card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L300-L330
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L300-L330

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_right_degree_eq_incident_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V} :
    paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u =
        (paper11K3IncidentSupports G D hCan hmax u).card := by sorry
