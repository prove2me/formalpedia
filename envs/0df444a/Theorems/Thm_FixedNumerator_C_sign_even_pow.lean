-- Prove2me | Theorems.Thm_FixedNumerator_C_sign_even_pow
-- name    : FixedNumerator.C_sign_even_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:30.287367+00:00
-- url     : https://prove2.me/theorems/95e0d4d0-9023-40af-99cc-8c54f4d670e7
-- title:
--   Fixed Numerator: C sign even pow
-- statement:
--   For even `k`, `(N π^k - 1)/4` is even, so `(-1)^{C(a, π^k)} = 1`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L95-L106
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L95-L106

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.C_sign_even_pow {π : GaussianInt} (hπ : IsPrimary π) (a : GaussianInt) {k : ℕ}
    (hk : Even k) : (-1 : ℂ) ^ C a (π ^ k) = 1 := by sorry
