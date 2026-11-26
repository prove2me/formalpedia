-- Prove2me | Theorems.Thm_FixedOrderFactor_rootOfUnity_eq_omega
-- name    : FixedOrderFactor.rootOfUnity_eq_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:56.9386+00:00
-- url     : https://prove2.me/theorems/49920d92-d6a7-4c14-9c56-1a54dce20113
-- title:
--   Fixed Order Factor: root Of Unity eq omega
-- statement:
--   The Fixed Order Factor construction uses the root Of Unity eq omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L28-L29
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L28-L29

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.rootOfUnity_eq_omega (r j : ℕ) : rootOfUnity r j = ω r ^ j := by sorry
