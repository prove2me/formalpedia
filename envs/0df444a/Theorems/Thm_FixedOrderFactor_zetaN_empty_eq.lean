-- Prove2me | Theorems.Thm_FixedOrderFactor_zetaN_empty_eq
-- name    : FixedOrderFactor.zetaN_empty_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:49:41.878333+00:00
-- url     : https://prove2.me/theorems/aedd066b-0272-52a2-a913-ec81c32815eb
-- title:
--   Fixed Order Factor: zeta N empty eq
-- statement:
--   The Fixed Order Factor construction uses the zeta N empty eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L30-L36
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L30-L36

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.zetaN_empty_eq {s : ℕ} (hs : s ≠ 0) : zetaN ∅ s = ∑' n : ℕ, 1 / (n : ℝ) ^ s := by sorry
