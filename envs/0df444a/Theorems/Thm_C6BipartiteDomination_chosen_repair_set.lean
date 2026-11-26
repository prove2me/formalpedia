-- Prove2me | Theorems.Thm_C6BipartiteDomination_chosen_repair_set
-- name    : C6BipartiteDomination.chosen_repair_set
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T21:49:44.799471+00:00
-- url     : https://prove2.me/theorems/ba11776e-f47e-4c09-bc8f-3df5ce884a90
-- title:
--   C6 Bipartite Domination: chosen repair set
-- statement:
--   The C6 Bipartite Domination construction uses the chosen repair set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L250-L275
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L250-L275

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.chosen_repair_set
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {w : V} (hw : w ∈ SPart G D)
    (ha : externalCharge G D w < 0) :
    ∃ R : Finset V,
      (∀ u, ChosenRepairRelation G D w R u → IsRepairVertex G D w u) ∧
      ((kCharge G D w = 3 ∧ R.card = 2) ∨
       (kCharge G D w = 4 ∧ R.card = 2) ∨
       (kCharge G D w = 3 ∧ R.card = 1)) := by sorry
