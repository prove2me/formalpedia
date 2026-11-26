-- Prove2me | Theorems.Thm_C6BipartiteDomination_ZPart_disjoint_BPart
-- name    : C6BipartiteDomination.ZPart_disjoint_BPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:49:11.167681+00:00
-- url     : https://prove2.me/theorems/e279865d-b15c-469b-b5d1-ae61c48b429a
-- title:
--   C6 Bipartite Domination: ZPart disjoint BPart
-- statement:
--   The C6 Bipartite Domination construction uses the ZPart disjoint BPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L82-L86
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A9.lean#L82-L86

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.ZPart_disjoint_BPart (D : Finset V) :
    Disjoint (ZPart G D) (BPart G D) := by sorry
