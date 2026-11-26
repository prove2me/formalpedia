-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3_left_debt_bound
-- name    : C6BipartiteDomination.paper11K3_left_debt_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:30.164882+00:00
-- url     : https://prove2.me/theorems/901cfa1d-9c6e-4257-bf1c-c85df034833c
-- title:
--   C6 Bipartite Domination: paper11 K3 left debt bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 left debt bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L348-L369
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L348-L369

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3_left_debt_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    -externalCharge G D w ≤
      if paper11LeftDegree (paper11K3Edges G D hCan hmax)
          (paper11K3RightVertices G D hCan hmax) w = 1 then 4 else 7 := by sorry
