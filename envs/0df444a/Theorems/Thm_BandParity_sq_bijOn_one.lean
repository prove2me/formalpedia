-- Prove2me | Theorems.Thm_BandParity_sq_bijOn_one
-- name    : BandParity.sq_bijOn_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:39.948418+00:00
-- url     : https://prove2.me/theorems/9910c18b-94c0-4e0c-9d77-227af97729d4
-- title:
--   Band Parity: sq bij On one
-- statement:
--   The Band Parity construction uses the sq bij On one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L156-L158
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L156-L158

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

theorem BandParity.sq_bijOn_one (hp8 : p % 8 = 5) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p)) (cls χ 1 : Set (ZMod p)) := by sorry
