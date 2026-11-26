-- Prove2me | Theorems.Thm_C6BipartiteDomination_paper11_chosen_profile
-- name    : C6BipartiteDomination.paper11_chosen_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:23.754561+00:00
-- url     : https://prove2.me/theorems/5f266cbb-327b-5ae6-90f2-8ff60bd1167f
-- title:
--   C6 Bipartite Domination: paper11 chosen profile
-- statement:
--   The C6 Bipartite Domination construction uses the paper11 chosen profile property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L232-L246
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L232-L246

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.paper11_chosen_profile {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ SPart G D) (ha : externalCharge G D w < 0) :
    ((kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2) ∨
      (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 1) ∨
      (kCharge G D w = 4 ∧ betaCharge G D w = 2 ∧
        (paperChosenRepairSet G D hCan hmax w).card = 2)) := by sorry
