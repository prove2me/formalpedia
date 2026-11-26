-- Prove2me | Theorems.Thm_FixedOrderFactor_conj_omega
-- name    : FixedOrderFactor.conj_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:05.947677+00:00
-- url     : https://prove2.me/theorems/cb4f5569-efcc-4227-abb2-5a48db9ff4ae
-- title:
--   Fixed Order Factor: conj omega
-- statement:
--   The Fixed Order Factor construction uses the conj omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L22-L26
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L22-L26

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.conj_omega (r : ℕ) : starRingEnd ℂ (ω r) = (ω r)⁻¹ := by sorry
