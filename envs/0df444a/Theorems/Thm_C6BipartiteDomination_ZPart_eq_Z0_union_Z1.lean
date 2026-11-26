-- Prove2me | Theorems.Thm_C6BipartiteDomination_ZPart_eq_Z0_union_Z1
-- name    : C6BipartiteDomination.ZPart_eq_Z0_union_Z1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:29.329966+00:00
-- url     : https://prove2.me/theorems/0e2eaeac-5b74-407a-8703-bb7713307a40
-- title:
--   C6 Bipartite Domination: ZPart eq Z0 union Z1
-- statement:
--   The C6 Bipartite Domination construction uses the ZPart eq Z0 union Z1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L67-L85
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L67-L85

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.ZPart_eq_Z0_union_Z1 (D : Finset V) :
    ZPart G D = Z0Part G D ∪ Z1Part G D := by sorry
