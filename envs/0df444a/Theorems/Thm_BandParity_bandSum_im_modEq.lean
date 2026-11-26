-- Prove2me | Theorems.Thm_BandParity_bandSum_im_modEq
-- name    : BandParity.bandSum_im_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:28.383523+00:00
-- url     : https://prove2.me/theorems/148521b7-aaf6-58ba-a95c-a2596ccb4804
-- title:
--   Band Parity: band Sum im mod Eq
-- statement:
--   **Theorem A, imaginary part.** `e ≡ κ (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L91-L93
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L91-L93

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.bandSum_im_modEq (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] := by sorry
