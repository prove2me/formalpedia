-- Prove2me | Theorems.Thm_C6BipartiteDomination_zpart_subset_selected
-- name    : C6BipartiteDomination.zpart_subset_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:17.980798+00:00
-- url     : https://prove2.me/theorems/55c0a6e5-1034-42ea-a5a6-6a828c64f148
-- title:
--   C6 Bipartite Domination: zpart subset selected
-- statement:
--   The C6 Bipartite Domination construction uses the zpart subset selected property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L158-L160
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L158-L160

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.zpart_subset_selected (D : Finset V) : ZPart G D ⊆ D := by sorry
