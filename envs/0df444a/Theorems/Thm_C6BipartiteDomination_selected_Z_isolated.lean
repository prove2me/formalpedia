-- Prove2me | Theorems.Thm_C6BipartiteDomination_selected_Z_isolated
-- name    : C6BipartiteDomination.selected_Z_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:46:59.917988+00:00
-- url     : https://prove2.me/theorems/c7c5a261-9dec-4a8f-8262-e0a82af49518
-- title:
--   C6 Bipartite Domination: selected Z isolated
-- statement:
--   The C6 Bipartite Domination construction uses the selected Z isolated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L60-L62
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A7.lean#L60-L62

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.selected_Z_isolated {D : Finset V} {z v : V}
    (hz : z ∈ ZPart G D) (hv : v ∈ D) : ¬ G.Adj z v := by sorry
