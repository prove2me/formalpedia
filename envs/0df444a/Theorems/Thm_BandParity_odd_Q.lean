-- Prove2me | Theorems.Thm_BandParity_odd_Q
-- name    : BandParity.odd_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:27.68517+00:00
-- url     : https://prove2.me/theorems/ed8905ad-f9f4-52ee-b4ad-0c6662c33fd6
-- title:
--   Band Parity: odd Q
-- statement:
--   The Band Parity construction uses the odd Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L357-L360
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L357-L360

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hp hχ

theorem BandParity.odd_Q (hp8 : p % 8 = 5) : Odd (Q p) := by sorry
