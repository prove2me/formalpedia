-- Prove2me | Theorems.Thm_C6BipartiteDomination_wb_card_eq
-- name    : C6BipartiteDomination.wb_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:50.102667+00:00
-- url     : https://prove2.me/theorems/c2e08d86-436a-440e-92b9-4b0fc0877f5f
-- title:
--   C6 Bipartite Domination: wb card eq
-- statement:
--   The C6 Bipartite Domination construction uses the wb card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L139-L173
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L139-L173

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.wb_card_eq (D : Finset V)
    (hCan : CanonicalTwoLevelOptimum G D) :
    (WBPart G D).card =
      2 * (BPart G D).card +
        (∑ b ∈ BPart G D, xCharge G D b) + (SPart G D).card := by sorry
