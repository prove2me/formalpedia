-- Prove2me | Theorems.Thm_FixedOrderFactor_zetaN_empty_two_mul
-- name    : FixedOrderFactor.zetaN_empty_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:41.849418+00:00
-- url     : https://prove2.me/theorems/704d1e9b-d328-5c68-9aee-3df3b2ca311c
-- title:
--   Fixed Order Factor: zeta N empty two mul
-- statement:
--   The Fixed Order Factor construction uses the zeta N empty two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L38-L41
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Values.lean#L38-L41

module
public import Definitions.Def_FixedOrderFactor_Order
public import Definitions.Def_FixedOrderFactor_Values
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.zetaN_empty_two_mul {k : ℕ} (hk : k ≠ 0) :
    zetaN ∅ (2 * k) = (-1) ^ (k + 1) * 2 ^ (2 * k - 1) * π ^ (2 * k) *
      (bernoulli (2 * k) : ℝ) / (2 * k).factorial := by sorry
