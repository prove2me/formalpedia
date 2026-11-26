-- Prove2me | Theorems.Thm_FixedOrderFactor_not_pow_succ_dvd_sq_sub_one
-- name    : FixedOrderFactor.not_pow_succ_dvd_sq_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:56:02.23283+00:00
-- url     : https://prove2.me/theorems/00d9cc5c-2eb4-4e13-967b-656aa63ec625
-- title:
--   Fixed Order Factor: not pow succ dvd sq sub one
-- statement:
--   If `x` is a unit modulo `2r` with `x² ≡ 1 + r (mod 2r)`, then `2^{v₂(r) + 1} ∤ x² - 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L225-L240
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/FixedOrderFactor/Bias.lean#L225-L240

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias
set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor

theorem FixedOrderFactor.not_pow_succ_dvd_sq_sub_one {r x : ℕ} (hr : 0 < r)
    (hsq : x ^ 2 % (2 * r) = (1 + r) % (2 * r))
    (hdvd : ((2 ^ (r.factorization 2 + 1) : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - 1) : False := by sorry
