-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_all_compensation_subset_nonnegative
-- name    : C6BipartiteDomination.paper11_all_compensation_subset_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:00:45.407328+00:00
-- url     : https://prove2.me/theorems/b13a2a8c-a08d-43d4-b3ce-2ebbba749911
-- title:
--   C6 Bipartite Domination: paper11 all compensation subset nonnegative
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 all compensation subset nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L707-L719
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11_2.lean#L707-L719

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_all_compensation_subset_nonnegative {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    paper11AllCompensation G D hCan hmax ⊆
      paper11NonnegativeSupports G D := by sorry
