-- Prove2me | Theorems.Thm_BandParity_val_neg_of_ne_zero
-- name    : BandParity.val_neg_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:06.994667+00:00
-- url     : https://prove2.me/theorems/9d62ba51-1667-4e09-8fc9-2dca5955a4c2
-- title:
--   Band Parity: val neg of ne zero
-- statement:
--   For `n ≠ 0`, `(-n).val = p - n.val`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L65-L68
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L65-L68

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem BandParity.val_neg_of_ne_zero {n : ZMod p} (hn : n ≠ 0) : (-n).val = p - n.val := by sorry
