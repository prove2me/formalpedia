-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
-- name    : C6BipartiteDomination.mem_paper11K3Supports
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:55:30.313808+00:00
-- url     : https://prove2.me/theorems/41423193-acf4-44f8-8b24-f688bfaa3a0b
-- title:
--   C6 Bipartite Domination: mem paper11 K3 Supports
-- statement:
--   The C6 Bipartite Domination construction uses the mem paper11 K3 Supports property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L211-L215
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L211-L215

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_paper11K3Supports {D : Finset V} {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    w ∈ SPart G D ∧ externalCharge G D w < 0 ∧ kCharge G D w = 3 := by sorry
