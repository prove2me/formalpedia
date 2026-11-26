-- Prove2me | Theorems.Thm_BandParity_card_class_mul
-- name    : BandParity.card_class_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:14.584949+00:00
-- url     : https://prove2.me/theorems/be300ef9-6d94-5a44-9521-4d75159c38f4
-- title:
--   Band Parity: card class mul
-- statement:
--   Multiplying by `c` moves `C_z` onto `C_{χ(c) z}`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L89-L96
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L89-L96

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.card_class_mul {c : ZMod p} (hc : c ≠ 0) (z : GaussianInt) :
    (univ.filter (fun n : ZMod p => χ n = χ c * z)).card =
      (univ.filter (fun n : ZMod p => χ n = z)).card := by sorry
