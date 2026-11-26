-- Prove2me | Theorems.Thm_FixedNumerator_C_sign_congr
-- name    : FixedNumerator.C_sign_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:35:08.602181+00:00
-- url     : https://prove2.me/theorems/7dc9914c-5300-554e-b153-9632314cb0d4
-- title:
--   Fixed Numerator: C sign congr
-- statement:
--   The sign `(-1)^{C(a, c)}` depends only on the class of a primary `a` modulo `4`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L86-L90
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Primary.lean#L86-L90

module
public import Definitions.Def_FixedNumerator_Defs
public import Definitions.Def_FixedNumerator_Primary
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset
open FixedNumerator

theorem FixedNumerator.C_sign_congr {a b c : GaussianInt} (hb : IsPrimary b) (h : (4 : GaussianInt) ∣ a - b) :
    (-1 : ℂ) ^ C a c = (-1 : ℂ) ^ C b c := by sorry
