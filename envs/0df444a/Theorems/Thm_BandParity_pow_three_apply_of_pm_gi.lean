-- Prove2me | Theorems.Thm_BandParity_pow_three_apply_of_pm_gi
-- name    : BandParity.pow_three_apply_of_pm_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:11.930576+00:00
-- url     : https://prove2.me/theorems/d118b140-1f1d-4d04-90ae-8ebd06fdd354
-- title:
--   Band Parity: pow three apply of pm gi
-- statement:
--   The conjugate character: `χ ^ 3` takes the value `-χ(a)` where `χ(a) = ± i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L41-L45
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L41-L45

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem BandParity.pow_three_apply_of_pm_gi (χ : MulChar (ZMod p) GaussianInt) {a : ZMod p}
    (h : χ a = gi ∨ χ a = -gi) : (χ ^ 3) a = -χ a := by sorry
