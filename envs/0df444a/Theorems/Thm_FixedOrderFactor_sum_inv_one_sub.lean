-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_inv_one_sub
-- name    : FixedOrderFactor.sum_inv_one_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:50:52.951867+00:00
-- url     : https://prove2.me/theorems/0909a9f7-55cb-5b17-bd92-64552d27dd56
-- title:
--   Fixed Order Factor: sum inv one sub
-- statement:
--   `∑_{z^r = 1} 1/(1 - z x) = r/(1 - x^r)`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L37-L56
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Local.lean#L37-L56

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Local
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology Complex Finset
open FixedOrderFactor

theorem FixedOrderFactor.sum_inv_one_sub {r : ℕ} (hr : 0 < r) {x : ℂ} (hx : x ^ r ≠ 1) :
    ∑ j ∈ range r, 1 / (1 - rootOfUnity r j * x) = r / (1 - x ^ r) := by sorry
