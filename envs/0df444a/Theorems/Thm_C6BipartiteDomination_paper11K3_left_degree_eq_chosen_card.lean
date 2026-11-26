-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_left_degree_eq_chosen_card
-- name    : C6BipartiteDomination.paper11K3_left_degree_eq_chosen_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:44.694514+00:00
-- url     : https://prove2.me/theorems/51745e73-fd05-440d-8110-8635bc605585
-- title:
--   C6 Bipartite Domination: paper11 K3 left degree eq chosen card
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 left degree eq chosen card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L269-L298
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L269-L298

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_left_degree_eq_chosen_card {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w =
        (paperChosenRepairSet G D hCan hmax w).card := by sorry
