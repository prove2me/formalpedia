-- Prove2me | Theorems.Thm_BandParity_two_mul_mapsTo_gi
-- name    : BandParity.two_mul_mapsTo_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:00.198158+00:00
-- url     : https://prove2.me/theorems/e7cc26ca-4f41-57e9-a6c0-c013fbce7a3e
-- title:
--   Band Parity: two mul maps To gi
-- statement:
--   The Band Parity construction uses the two mul maps To gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L151-L154
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L151-L154

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

theorem BandParity.two_mul_mapsTo_gi (hpin : χ 2 = gi) :
    Set.MapsTo (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) := by sorry
