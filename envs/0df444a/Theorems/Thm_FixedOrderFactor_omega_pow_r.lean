-- Prove2me | Theorems.Thm_FixedOrderFactor_omega_pow_r
-- name    : FixedOrderFactor.omega_pow_r
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:49.019808+00:00
-- url     : https://prove2.me/theorems/12398c0a-44bb-4754-9b66-4181d40b8620
-- title:
--   Fixed Order Factor: omega pow r
-- statement:
--   The Fixed Order Factor construction uses the omega pow r property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L17-L18
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L17-L18

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.omega_pow_r {r : ℕ} (hr : 0 < r) : ω r ^ r = 1 := by sorry
