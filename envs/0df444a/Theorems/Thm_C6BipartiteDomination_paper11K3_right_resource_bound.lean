-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_right_resource_bound
-- name    : C6BipartiteDomination.paper11K3_right_resource_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:34.576983+00:00
-- url     : https://prove2.me/theorems/9ec08a44-b667-5485-89d8-9d0954269734
-- title:
--   C6 Bipartite Domination: paper11 K3 right resource bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 right resource bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L889-L914
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L889-L914

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_right_resource_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    (if paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 1 then 4 else 11) ≤
      paper11K3AvailableResource G D hCan hmax u := by sorry
