-- Prove2me | Theorems.Thm_BandParity_card_class_eq
-- name    : BandParity.card_class_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:21.993787+00:00
-- url     : https://prove2.me/theorems/244a64ff-b824-486b-989f-7d6b8caab474
-- title:
--   Band Parity: card class eq
-- statement:
--   Every class `C_z`, `z ∈ {1, i, -1, -i}`, has the size of `C_1`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L99-L122
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L99-L122

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

theorem BandParity.card_class_eq (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (univ.filter (fun n : ZMod p => χ n = z)).card =
      (univ.filter (fun n : ZMod p => χ n = 1)).card := by sorry
