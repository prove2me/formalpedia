-- Prove2me | Theorems.Thm_BandParity_fixed_base_collapse
-- name    : BandParity.fixed_base_collapse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:46.519935+00:00
-- url     : https://prove2.me/theorems/4dfe1eaa-2808-50a0-bb94-7ddc5d16ed55
-- title:
--   Band Parity: fixed base collapse
-- statement:
--   **Proposition 4.1 (fixed-base collapse).**
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L40-L62
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L40-L62

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem BandParity.fixed_base_collapse (χ : MulChar (ZMod p) R) {b : ZMod p} (hb : b ≠ 0) :
    (p : R) * χ b * floorSum χ b = ((b.val : R) * χ b - 1) * T χ := by sorry
