-- Prove2me | Theorems.Thm_BandParity_sq_mapsTo_gi
-- name    : BandParity.sq_mapsTo_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:46.48937+00:00
-- url     : https://prove2.me/theorems/57226da3-842d-5655-a8c3-7153953a8fe1
-- title:
--   Band Parity: sq maps To gi
-- statement:
--   The Band Parity construction uses the sq maps To gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L146-L148
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L146-L148

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

theorem BandParity.sq_mapsTo_gi : Set.MapsTo (fun x : ZMod p => x ^ 2) (cls χ gi : Set (ZMod p))
    (cls χ (-1) : Set (ZMod p)) := by sorry
