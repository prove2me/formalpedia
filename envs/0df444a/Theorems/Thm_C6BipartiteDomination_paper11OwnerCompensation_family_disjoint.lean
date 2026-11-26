-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_family_disjoint
-- name    : C6BipartiteDomination.paper11OwnerCompensation_family_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:33.51626+00:00
-- url     : https://prove2.me/theorems/c9851e50-1005-42ac-9ad6-f0b4fe381e54
-- title:
--   C6 Bipartite Domination: paper11 Owner Compensation family disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Owner Compensation family disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L539-L559
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L539-L559

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11OwnerCompensation_family_disjoint {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11AllRepairOwners G D hCan hmax : Set V).PairwiseDisjoint
      (paper11OwnerCompensation G D hCan hmax) := by sorry
