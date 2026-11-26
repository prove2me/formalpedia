-- Prove2me | Theorems.Thm_C6BipartiteDomination_bpart_zpart_partition
-- name    : C6BipartiteDomination.bpart_zpart_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:16.819387+00:00
-- url     : https://prove2.me/theorems/c35f1906-6273-5eb2-aa01-3cdc0769ce4c
-- title:
--   C6 Bipartite Domination: bpart zpart partition
-- statement:
--   The C6 Bipartite Domination construction uses the bpart zpart partition property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L162-L174
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/MainResults.lean#L162-L174

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.bpart_zpart_partition (D : Finset V) :
    D = BPart G D ∪ ZPart G D := by sorry
