-- Prove2me | Theorems.Thm_C6BipartiteDomination_selected_partition_card
-- name    : C6BipartiteDomination.selected_partition_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:22.225883+00:00
-- url     : https://prove2.me/theorems/9bdfcdf7-d3b6-4bac-b7bf-eafaf1fc0393
-- title:
--   C6 Bipartite Domination: selected partition card
-- statement:
--   The C6 Bipartite Domination construction uses the selected partition card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L176-L192
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L176-L192

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.selected_partition_card (D : Finset V) :
    D.card = (BPart G D).card + (Z0Part G D).card + (Z1Part G D).card := by sorry
