-- Prove2me | Theorems.Thm_C6BipartiteDomination_sum_beta_eq_sum_s
-- name    : C6BipartiteDomination.sum_beta_eq_sum_s
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:02.191098+00:00
-- url     : https://prove2.me/theorems/663468b7-2b1d-40b9-891c-c767838672ea
-- title:
--   C6 Bipartite Domination: sum beta eq sum s
-- statement:
--   The C6 Bipartite Domination construction uses the sum beta eq sum s property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L183-L186
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L183-L186

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.sum_beta_eq_sum_s (D : Finset V) :
    (∑ w ∈ SPart G D, betaCharge G D w) =
      ∑ b ∈ BPart G D, sCharge G D b := by sorry
