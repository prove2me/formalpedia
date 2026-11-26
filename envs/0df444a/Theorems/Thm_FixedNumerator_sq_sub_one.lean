-- Prove2me | Theorems.Thm_FixedNumerator_sq_sub_one
-- name    : FixedNumerator.sq_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:25.805483+00:00
-- url     : https://prove2.me/theorems/17766900-ea86-4608-86e3-f420078b22f1
-- title:
--   Fixed Numerator: sq sub one
-- statement:
--   A primary `π` satisfies `π² ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L45-L51
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L45-L51

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.sq_sub_one {π : GaussianInt} (hπ : IsPrimary π) : (4 : GaussianInt) ∣ π ^ 2 - 1 := by sorry
