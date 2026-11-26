-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11OwnerCompensation_subset_S
-- name    : C6BipartiteDomination.paper11OwnerCompensation_subset_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:03.317476+00:00
-- url     : https://prove2.me/theorems/6629767a-3fa5-4d19-8ed8-94aded0d7db4
-- title:
--   C6 Bipartite Domination: paper11 Owner Compensation subset S
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 Owner Compensation subset S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L484-L496
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L484-L496

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11OwnerCompensation_subset_S {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u q : V}
    (huB : u ∈ BPart G D)
    (hq : q ∈ paper11OwnerCompensation G D hCan hmax u) :
    q ∈ SPart G D := by sorry
