-- Prove2me | Theorems.Thm_C6BipartiteDomination_support_union_card_le_degree
-- name    : C6BipartiteDomination.support_union_card_le_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:25.260086+00:00
-- url     : https://prove2.me/theorems/083e4284-9f85-5973-8855-15a256892de1
-- title:
--   C6 Bipartite Domination: support union card le degree
-- statement:
--   The C6 Bipartite Domination construction uses the support union card le degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L270-L290
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L270-L290

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.support_union_card_le_degree
    {D : Finset V} {w : V} :
    kCharge G D w + betaCharge G D w ≤ degreeTo G Finset.univ w := by sorry
