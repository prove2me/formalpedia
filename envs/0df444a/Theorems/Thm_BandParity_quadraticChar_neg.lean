-- Prove2me | Theorems.Thm_BandParity_quadraticChar_neg
-- name    : BandParity.quadraticChar_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:22.710445+00:00
-- url     : https://prove2.me/theorems/e96ce6fc-b275-4108-8874-294d39f90d25
-- title:
--   Band Parity: quadratic Char neg
-- statement:
--   The Band Parity construction uses the quadratic Char neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L47-L51
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L47-L51

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.quadraticChar_neg (hp4 : p % 4 = 1) (x : ZMod p) :
    quadraticChar (ZMod p) (-x) = quadraticChar (ZMod p) x := by sorry
