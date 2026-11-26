-- Prove2me | Theorems.Thm_C6BipartiteDomination_Z0_Z1_disjoint
-- name    : C6BipartiteDomination.Z0_Z1_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:43:42.356329+00:00
-- url     : https://prove2.me/theorems/9467fcdf-73e7-4620-9560-be00c0a83246
-- title:
--   C6 Bipartite Domination: Z0 Z1 disjoint
-- statement:
--   The C6 Bipartite Domination construction uses the Z0 Z1 disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L87-L93
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A5.lean#L87-L93

import Definitions.Def_C6BipartiteDomination_A4
import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.Z0_Z1_disjoint (D : Finset V) :
    Disjoint (Z0Part G D) (Z1Part G D) := by sorry
