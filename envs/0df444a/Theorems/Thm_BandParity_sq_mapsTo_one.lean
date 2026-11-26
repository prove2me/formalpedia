-- Prove2me | Theorems.Thm_BandParity_sq_mapsTo_one
-- name    : BandParity.sq_mapsTo_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:53.965218+00:00
-- url     : https://prove2.me/theorems/9abf3b78-e843-434d-a9f3-999727682d9b
-- title:
--   Band Parity: sq maps To one
-- statement:
--   The Band Parity construction uses the sq maps To one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L141-L143
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L141-L143

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
omit hχ

theorem BandParity.sq_mapsTo_one : Set.MapsTo (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p))
    (cls χ 1 : Set (ZMod p)) := by sorry
