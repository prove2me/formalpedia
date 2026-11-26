-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K4_left_degree_eq_two
-- name    : C6BipartiteDomination.paper11K4_left_degree_eq_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:41.524784+00:00
-- url     : https://prove2.me/theorems/cddd94c6-d8ad-4e47-9f04-23ee6cb85992
-- title:
--   C6 Bipartite Domination: paper11 K4 left degree eq two
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K4 left degree eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L144-L153
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L144-L153

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K4_left_degree_eq_two {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    paper11LeftDegree (paper11K4Edges G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) w = 2 := by sorry
