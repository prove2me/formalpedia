-- Prove2me | Theorems.Thm_BandParity_quartic_ext
-- name    : BandParity.quartic_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:14.055147+00:00
-- url     : https://prove2.me/theorems/d459432b-223d-4323-9257-b42fa67e330b
-- title:
--   Band Parity: quartic ext
-- statement:
--   Two quartic characters with the same value at a generator coincide.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L33-L37
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L33-L37

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.quartic_ext {χ ψ : MulChar (ZMod p) GaussianInt} {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) (h : χ g = ψ g) : χ = ψ := by sorry
