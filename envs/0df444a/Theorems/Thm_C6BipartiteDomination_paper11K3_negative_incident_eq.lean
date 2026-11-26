-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_negative_incident_eq
-- name    : C6BipartiteDomination.paper11K3_negative_incident_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:54.401178+00:00
-- url     : https://prove2.me/theorems/8fb1af93-6542-4aff-9113-21c1d20d74cd
-- title:
--   C6 Bipartite Domination: paper11 K3 negative incident eq
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 negative incident eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L371-L407
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L371-L407

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_negative_incident_eq {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11NegativeIncidentSupports G D hCan hmax u =
      paper11K3IncidentSupports G D hCan hmax u := by sorry
