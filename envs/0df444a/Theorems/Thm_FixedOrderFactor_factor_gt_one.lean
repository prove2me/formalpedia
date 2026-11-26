-- Prove2me | Theorems.Thm_FixedOrderFactor_factor_gt_one
-- name    : FixedOrderFactor.factor_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:16.549902+00:00
-- url     : https://prove2.me/theorems/154e6ae4-867e-4ddf-a750-fb63cb284962
-- title:
--   Fixed Order Factor: factor gt one
-- statement:
--   The Euler factor `(1 + y)/(1 - y)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L36-L37
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Order.lean#L36-L37

module
public import Definitions.Def_FixedOrderFactor_Model
public import Definitions.Def_FixedOrderFactor_Order
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Finset
open FixedOrderFactor

theorem FixedOrderFactor.factor_gt_one {y : ℝ} (h0 : 0 < y) (h1 : y < 1) : 1 < (1 + y) / (1 - y) := by sorry
