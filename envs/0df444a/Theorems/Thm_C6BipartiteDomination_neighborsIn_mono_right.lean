-- Prove2me | Theorems.Thm_C6BipartiteDomination_neighborsIn_mono_right
-- name    : C6BipartiteDomination.neighborsIn_mono_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:52.230085+00:00
-- url     : https://prove2.me/theorems/b5b09823-fe25-4067-a5b4-919ac28f6c59
-- title:
--   C6 Bipartite Domination: neighbors In mono right
-- statement:
--   The C6 Bipartite Domination construction uses the neighbors In mono right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L49-L54
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L49-L54

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.neighborsIn_mono_right {S T₁ T₂ : Finset V} (h : T₁ ⊆ T₂) :
    neighborsIn G S T₁ ⊆ neighborsIn G S T₂ := by sorry
