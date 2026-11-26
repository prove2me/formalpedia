-- Prove2me | Theorems.Thm_BandParity_quartic_eq_or_eq_pow_three
-- name    : BandParity.quartic_eq_or_eq_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:38.545202+00:00
-- url     : https://prove2.me/theorems/146a7d7c-293d-4b10-9315-a65e9808f111
-- title:
--   Band Parity: quartic eq or eq pow three
-- statement:
--   **The two quartic characters.** Every quartic character modulo `p` is `χ` or its
--   conjugate `χ ^ 3`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L82-L91
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L82-L91

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.quartic_eq_or_eq_pow_three {χ ψ : MulChar (ZMod p) GaussianInt}
    (hχ : orderOf χ = 4) (hψ : orderOf ψ = 4) : ψ = χ ∨ ψ = χ ^ 3 := by sorry
