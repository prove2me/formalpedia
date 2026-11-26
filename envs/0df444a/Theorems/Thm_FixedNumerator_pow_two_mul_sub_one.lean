-- Prove2me | Theorems.Thm_FixedNumerator_pow_two_mul_sub_one
-- name    : FixedNumerator.pow_two_mul_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:15.273586+00:00
-- url     : https://prove2.me/theorems/4c5a6091-7d56-5cfb-8ab1-22385f3f0241
-- title:
--   Fixed Numerator: pow two mul sub one
-- statement:
--   `π^(2k) ≡ 1 (mod 4)` for primary `π`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L54-L57
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L54-L57

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.pow_two_mul_sub_one {π : GaussianInt} (hπ : IsPrimary π) (k : ℕ) :
    (4 : GaussianInt) ∣ π ^ (2 * k) - 1 := by sorry
