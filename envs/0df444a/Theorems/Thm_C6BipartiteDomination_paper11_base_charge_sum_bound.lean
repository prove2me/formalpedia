-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_base_charge_sum_bound
-- name    : C6BipartiteDomination.paper11_base_charge_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:17.284785+00:00
-- url     : https://prove2.me/theorems/a562a51f-9b92-490c-a7c1-ea4ff5c969e0
-- title:
--   C6 Bipartite Domination: paper11 base charge sum bound
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 base charge sum bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L796-L835
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L796-L835

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_base_charge_sum_bound {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax, vertexCharge G D u) ≤
      ∑ u ∈ BPart G D, vertexCharge G D u := by sorry
