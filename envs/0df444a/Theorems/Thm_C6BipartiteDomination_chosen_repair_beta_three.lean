-- Prove2me | Theorems.Thm_C6BipartiteDomination_chosen_repair_beta_three
-- name    : C6BipartiteDomination.chosen_repair_beta_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:38.031013+00:00
-- url     : https://prove2.me/theorems/0c2e838a-c7c7-4b11-8ca6-c7ea34da3269
-- title:
--   C6 Bipartite Domination: chosen repair beta three
-- statement:
--   The C6 Bipartite Domination construction uses the chosen repair beta three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L184-L248
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A8.lean#L184-L248

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.chosen_repair_beta_three
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hβ : betaCharge G D w = 3) :
    ∃ u, IsRepairVertex G D w u := by sorry
