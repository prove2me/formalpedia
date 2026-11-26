-- Prove2me | Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
-- name    : C6BipartiteDomination.Z0_disjoint_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:47:08.363736+00:00
-- url     : https://prove2.me/theorems/8d35fb9f-073e-419d-ab66-ea36a70086f6
-- title:
--   C6 Bipartite Domination: Z0 disjoint B
-- statement:
--   The C6 Bipartite Domination construction uses the Z0 disjoint B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L64-L69
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L64-L69

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.Z0_disjoint_B {D : Finset V} :
    Disjoint (Z0Part G D) (BPart G D) := by sorry
