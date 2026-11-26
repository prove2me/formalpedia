-- Prove2me | Theorems.Thm_C6BipartiteDomination_PPart_subset_WBPart
-- name    : C6BipartiteDomination.PPart_subset_WBPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:45:20.937429+00:00
-- url     : https://prove2.me/theorems/b698891b-4903-5317-b804-5be3d0b35856
-- title:
--   C6 Bipartite Domination: PPart subset WBPart
-- statement:
--   The C6 Bipartite Domination construction uses the PPart subset WBPart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L78-L88
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean#L78-L88

import Definitions.Def_C6BipartiteDomination_A5
import Definitions.Def_C6BipartiteDomination_A6
set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.PPart_subset_WBPart (D : Finset V) : PPart G D ⊆ WBPart G D := by sorry
