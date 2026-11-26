-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_external_charge_sum_split
-- name    : C6BipartiteDomination.paper11_external_charge_sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:50.420356+00:00
-- url     : https://prove2.me/theorems/7bcacffe-8937-5a51-b112-f8410190acd5
-- title:
--   C6 Bipartite Domination: paper11 external charge sum split
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 external charge sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L721-L776
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L721-L776

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_external_charge_sum_split {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ w ∈ SPart G D, externalCharge G D w) =
      (∑ w ∈ paper11NegativeSupports G D, externalCharge G D w) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      (∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q) := by sorry
