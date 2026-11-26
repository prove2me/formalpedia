-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_sum_eq_owner_sums
-- name    : C6BipartiteDomination.paper11AllCompensation_sum_eq_owner_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:21.888048+00:00
-- url     : https://prove2.me/theorems/077e5388-3336-5af8-a499-ac4019c7337a
-- title:
--   C6 Bipartite Domination: paper11 All Compensation sum eq owner sums
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 All Compensation sum eq owner sums property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L579-L633
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L579-L633

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11AllCompensation_sum_eq_owner_sums {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax,
      ∑ q ∈ paper11OwnerCompensation G D hCan hmax u,
        externalCharge G D q) =
      ∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q := by sorry
