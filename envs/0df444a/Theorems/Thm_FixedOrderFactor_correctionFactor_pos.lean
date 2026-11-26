-- Prove2me | Theorems.Thm_FixedOrderFactor_correctionFactor_pos
-- name    : FixedOrderFactor.correctionFactor_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:51:53.917606+00:00
-- url     : https://prove2.me/theorems/d47b5f45-f152-451a-84c5-9e2604a4441d
-- title:
--   Fixed Order Factor: correction Factor pos
-- statement:
--   The Fixed Order Factor construction uses the correction Factor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L48-L49
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L48-L49

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.correctionFactor_pos (N : Finset Nat.Primes) {r : ℕ} (hr : 2 ≤ r) :
    0 < correctionFactor N r := by sorry
