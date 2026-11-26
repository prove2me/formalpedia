-- Prove2me | Theorems.Thm_C6BipartiteDomination_chosen_repairs_beta_two
-- name    : C6BipartiteDomination.chosen_repairs_beta_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:30.849837+00:00
-- url     : https://prove2.me/theorems/9a81d11c-091f-5229-9ee8-428a7c5bdefb
-- title:
--   C6 Bipartite Domination: chosen repairs beta two
-- statement:
--   The C6 Bipartite Domination construction uses the chosen repairs beta two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L103-L178
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L103-L178

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.chosen_repairs_beta_two
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) (hβ : betaCharge G D w = 2) :
    ∃ R : Finset V, R.card = 2 ∧
      ∀ u ∈ R, IsRepairVertex G D w u := by sorry
