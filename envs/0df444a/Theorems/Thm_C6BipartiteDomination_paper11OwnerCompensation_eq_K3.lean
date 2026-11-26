-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_eq_K3
-- name    : C6BipartiteDomination.paper11OwnerCompensation_eq_K3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:10.120408+00:00
-- url     : https://prove2.me/theorems/2b3bfea8-997c-4814-93c7-2bad35948695
-- title:
--   C6 Bipartite Domination: paper11 Owner Compensation eq K3
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Owner Compensation eq K3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L451-L459
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L451-L459

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11OwnerCompensation_eq_K3 {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11OwnerCompensation G D hCan hmax u =
      paper11K3Compensation G D hCan hmax u := by sorry
