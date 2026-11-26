-- Prove2me | Theorems.Thm_BandParity_orderOf_pow_three
-- name    : BandParity.orderOf_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:27.439095+00:00
-- url     : https://prove2.me/theorems/ed0f2777-7423-51a1-a6c9-3dc584b39aad
-- title:
--   Band Parity: order Of pow three
-- statement:
--   The Band Parity construction uses the order Of pow three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L28-L30
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L28-L30

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem BandParity.orderOf_pow_three {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4) :
    orderOf (χ ^ 3) = 4 := by sorry
