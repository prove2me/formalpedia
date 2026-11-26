-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11K3AvailableResource_sum_decomposition
-- name    : C6BipartiteDomination.paper11K3AvailableResource_sum_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:59:27.960014+00:00
-- url     : https://prove2.me/theorems/249a9469-7d19-52d1-bd70-da535f7ea94d
-- title:
--   C6 Bipartite Domination: paper11 K3 Available Resource sum decomposition
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 K3 Available Resource sum decomposition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L875-L887
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L875-L887

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11K3AvailableResource_sum_decomposition {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      paper11K3AvailableResource G D hCan hmax u) =
      (∑ u ∈ paper11K3RightVertices G D hCan hmax,
        (vertexCharge G D u +
          ∑ q ∈ paper11K3Compensation G D hCan hmax u,
            externalCharge G D q)) +
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by sorry
