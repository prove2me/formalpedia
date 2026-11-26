-- Prove2me | Theorems.Thm_BandParity_card_class
-- name    : BandParity.card_class
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:13.626813+00:00
-- url     : https://prove2.me/theorems/1ad4c74d-5f15-59a0-8399-f00e3761c0ea
-- title:
--   Band Parity: card class
-- statement:
--   **Class sizes.** Each class has `(p - 1)/4` elements.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L125-L143
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L125-L143

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

theorem BandParity.card_class (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    4 * (univ.filter (fun n : ZMod p => χ n = z)).card = p - 1 := by sorry
