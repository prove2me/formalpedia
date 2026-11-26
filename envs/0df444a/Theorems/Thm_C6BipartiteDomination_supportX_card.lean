-- Prove2me | Theorems.Thm_C6BipartiteDomination_supportX_card
-- name    : C6BipartiteDomination.supportX_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:40.050328+00:00
-- url     : https://prove2.me/theorems/882a602c-49dc-4afb-8211-049e468213f3
-- title:
--   C6 Bipartite Domination: support X card
-- statement:
--   The C6 Bipartite Domination construction uses the support X card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L32-L35
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L32-L35

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.supportX_card (D : Finset V) (w : V) :
    (supportX G D w).card = kCharge G D w := by sorry
