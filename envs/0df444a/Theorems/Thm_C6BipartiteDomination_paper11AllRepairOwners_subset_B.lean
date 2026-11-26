-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11AllRepairOwners_subset_B
-- name    : C6BipartiteDomination.paper11AllRepairOwners_subset_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:17.723099+00:00
-- url     : https://prove2.me/theorems/79a9a5d1-d5eb-4799-b885-d4a8c0fa1a04
-- title:
--   C6 Bipartite Domination: paper11 All Repair Owners subset B
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 All Repair Owners subset B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L530-L537
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L530-L537

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11AllRepairOwners_subset_B {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllRepairOwners G D hCan hmax ⊆ BPart G D := by sorry
