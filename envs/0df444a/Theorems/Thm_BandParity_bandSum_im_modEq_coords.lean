-- Prove2me | Theorems.Thm_BandParity_bandSum_im_modEq_coords
-- name    : BandParity.bandSum_im_modEq_coords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:06.44723+00:00
-- url     : https://prove2.me/theorems/f998fc38-e6c0-40bd-a86f-0ffe065d1998
-- title:
--   Band Parity: band Sum im mod Eq coords
-- statement:
--   **Coordinate Congruence, first form.** `e ≡ Q + k + t (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L101-L103
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L101-L103

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

theorem BandParity.bandSum_im_modEq_coords (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] := by sorry
