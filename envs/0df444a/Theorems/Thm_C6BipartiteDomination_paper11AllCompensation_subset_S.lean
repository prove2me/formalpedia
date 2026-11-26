-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11AllCompensation_subset_S
-- name    : C6BipartiteDomination.paper11AllCompensation_subset_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:41.65027+00:00
-- url     : https://prove2.me/theorems/bb4e3cdd-cf95-4529-a25e-eceac17f2f89
-- title:
--   C6 Bipartite Domination: paper11 All Compensation subset S
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 All Compensation subset S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L561-L568
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L561-L568

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11AllCompensation_subset_S {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆ SPart G D := by sorry
