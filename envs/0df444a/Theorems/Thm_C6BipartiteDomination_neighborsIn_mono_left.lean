-- Prove2me | Theorems.Thm_C6BipartiteDomination_neighborsIn_mono_left
-- name    : C6BipartiteDomination.neighborsIn_mono_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:41:30.637457+00:00
-- url     : https://prove2.me/theorems/bf046adc-07e0-4389-8d11-180a2fa18b12
-- title:
--   C6 Bipartite Domination: neighbors In mono left
-- statement:
--   The C6 Bipartite Domination construction uses the neighbors In mono left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L40-L47
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A3.lean#L40-L47

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

theorem C6BipartiteDomination.neighborsIn_mono_left {S₁ S₂ T : Finset V} (h : S₁ ⊆ S₂) :
    neighborsIn G S₁ T ⊆ neighborsIn G S₂ T := by sorry
