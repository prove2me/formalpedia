-- Prove2me | Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
-- name    : C6BipartiteDomination.mem_paper11K4Supports
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:04.614105+00:00
-- url     : https://prove2.me/theorems/6179eaa3-98c2-43b7-a67b-a31810b48537
-- title:
--   C6 Bipartite Domination: mem paper11 K4 Supports
-- statement:
--   The C6 Bipartite Domination construction uses the mem paper11 K4 Supports property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L217-L221
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/PaperSection11.lean#L217-L221

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.mem_paper11K4Supports {D : Finset V} {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    w ∈ SPart G D ∧ externalCharge G D w < 0 ∧ kCharge G D w = 4 := by sorry
