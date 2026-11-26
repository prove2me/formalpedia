-- Prove2me | Theorems.Thm_C6BipartiteDomination_outside_partition_card
-- name    : C6BipartiteDomination.outside_partition_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:22.042799+00:00
-- url     : https://prove2.me/theorems/1475ed4d-66f3-5b43-b86f-f6bdf00a12a4
-- title:
--   C6 Bipartite Domination: outside partition card
-- statement:
--   The C6 Bipartite Domination construction uses the outside partition card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L194-L216
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L194-L216

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.outside_partition_card (D : Finset V) :
    (Finset.univ \ D).card = (W0Part G D).card + (WBPart G D).card := by sorry
