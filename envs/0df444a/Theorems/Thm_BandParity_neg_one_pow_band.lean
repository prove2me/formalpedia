-- Prove2me | Theorems.Thm_BandParity_neg_one_pow_band
-- name    : BandParity.neg_one_pow_band
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:15.405971+00:00
-- url     : https://prove2.me/theorems/26eea163-f74e-4e62-8ad1-9a940b039cbd
-- title:
--   Band Parity: neg one pow band
-- statement:
--   **Parity dictionary.** `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L49-L51
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L49-L51

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.neg_one_pow_band (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) := by sorry
