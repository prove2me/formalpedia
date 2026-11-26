-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_owner_resource_sums_union
-- name    : C6BipartiteDomination.paper11_owner_resource_sums_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:35.914784+00:00
-- url     : https://prove2.me/theorems/5914aa8a-fce4-470f-a93e-e464c50b923c
-- title:
--   C6 Bipartite Domination: paper11 owner resource sums union
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 owner resource sums union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L860-L871
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L860-L871

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_owner_resource_sums_union {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) +
      ∑ u ∈ paper11K4RightVertices G D hCan hmax,
        paper11OwnerResource G D hCan hmax u =
      ∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        paper11OwnerResource G D hCan hmax u := by sorry
