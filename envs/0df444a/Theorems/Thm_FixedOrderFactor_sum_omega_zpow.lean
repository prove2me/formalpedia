-- Prove2me | Theorems.Thm_FixedOrderFactor_sum_omega_zpow
-- name    : FixedOrderFactor.sum_omega_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:55:15.061309+00:00
-- url     : https://prove2.me/theorems/dc369d03-3960-4223-b624-242f49278fe0
-- title:
--   Fixed Order Factor: sum omega zpow
-- statement:
--   `∑_{k<r} ω^{ke} = r` if `r ∣ e`, and `0` otherwise.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L32-L46
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/ModelPairs.lean#L32-L46

module
public import Definitions.Def_FixedOrderFactor_Defs
public import Definitions.Def_FixedOrderFactor_Pairs
public import Definitions.Def_FixedOrderFactor_ModelPairs
set_option autoImplicit true
@[expose] public section
public section
open Finset Complex
open FixedOrderFactor

theorem FixedOrderFactor.sum_omega_zpow {r : ℕ} (hr : 0 < r) (e : ℤ) :
    ∑ k : Fin r, ω r ^ ((k : ℤ) * e) = if (r : ℤ) ∣ e then (r : ℂ) else 0 := by sorry
