-- Prove2me | Theorems.Thm_BandParity_quadraticChar_eq_legendreSym
-- name    : BandParity.quadraticChar_eq_legendreSym
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:59.61404+00:00
-- url     : https://prove2.me/theorems/ad47a08c-4f8c-55dc-b623-32b4627b6b7d
-- title:
--   Band Parity: quadratic Char eq legendre Sym
-- statement:
--   The Band Parity construction uses the quadratic Char eq legendre Sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L53-L55
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L53-L55

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.quadraticChar_eq_legendreSym (x : ZMod p) :
    quadraticChar (ZMod p) x = legendreSym p (x.val : ℤ) := by sorry
