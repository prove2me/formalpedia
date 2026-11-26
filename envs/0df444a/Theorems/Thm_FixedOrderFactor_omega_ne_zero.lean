-- Prove2me | Theorems.Thm_FixedOrderFactor_omega_ne_zero
-- name    : FixedOrderFactor.omega_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:43.472158+00:00
-- url     : https://prove2.me/theorems/1dffae6a-7824-5336-ac51-c9c195b864f5
-- title:
--   Fixed Order Factor: omega ne zero
-- statement:
--   The Fixed Order Factor construction uses the omega ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L20-L20
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L20-L20

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.omega_ne_zero (r : ℕ) : ω r ≠ 0 := by sorry
