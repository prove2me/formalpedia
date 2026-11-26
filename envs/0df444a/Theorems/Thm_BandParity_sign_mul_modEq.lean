-- Prove2me | Theorems.Thm_BandParity_sign_mul_modEq
-- name    : BandParity.sign_mul_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:52.42677+00:00
-- url     : https://prove2.me/theorems/451e7f89-ec35-4dfa-9e48-4dc12ffa12d0
-- title:
--   Band Parity: sign mul mod Eq
-- statement:
--   For signs `a, b ∈ {± 1}`, `a b ≡ a + b - 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L26-L28
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L26-L28

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem BandParity.sign_mul_modEq {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b ≡ a + b - 1 [ZMOD 4] := by sorry
