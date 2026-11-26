-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11OwnerResource_sum_decomposition
-- name    : C6BipartiteDomination.paper11OwnerResource_sum_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:31.175013+00:00
-- url     : https://prove2.me/theorems/7c5e89ad-f323-492e-a180-d3cd3a516e35
-- title:
--   C6 Bipartite Domination: paper11 Owner Resource sum decomposition
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Owner Resource sum decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L845-L858
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L845-L858

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11OwnerResource_sum_decomposition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      paper11OwnerResource G D hCan hmax u) =
      (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
        vertexCharge G D u) +
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by sorry
