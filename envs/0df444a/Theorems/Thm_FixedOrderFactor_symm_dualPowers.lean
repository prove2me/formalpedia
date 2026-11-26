-- Prove2me | Theorems.Thm_FixedOrderFactor_symm_dualPowers
-- name    : FixedOrderFactor.symm_dualPowers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:47:07.075838+00:00
-- url     : https://prove2.me/theorems/2541ca03-0ede-5c16-899a-d8b5a50bab9a
-- title:
--   Fixed Order Factor: symm dual Powers
-- statement:
--   The Fixed Order Factor construction uses the symm dual Powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L40-L43
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Characters.lean#L40-L43

module
public import Mathlib
public import Definitions.Def_FixedOrderFactor_Characters
set_option autoImplicit true
@[expose] public section
public section
open Finset
open FixedOrderFactor
variable (p : ℕ) [Fact p.Prime]

theorem FixedOrderFactor.symm_dualPowers (r : ℕ) :
    (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod p) ℂ).symm (OrderDual.toDual (dualPowers p r))
      = powers p r := by sorry
