-- Prove2me | Theorems.Thm_BandParity_cosetSum_add_cosetSum_neg
-- name    : BandParity.cosetSum_add_cosetSum_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:18.121795+00:00
-- url     : https://prove2.me/theorems/bcd69e32-7b9b-5e01-a02e-8d4dadecbb3b
-- title:
--   Band Parity: coset Sum add coset Sum neg
-- statement:
--   Negation moves `C_z` onto `C_{-z}` when `χ` is odd.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L147-L167
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L147-L167

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
omit hχ

theorem BandParity.cosetSum_add_cosetSum_neg (hodd : χ (-1) = -1) (z : GaussianInt) (hz0 : z ≠ 0) :
    cosetSum χ z + cosetSum χ (-z) =
      p * (univ.filter (fun n : ZMod p => χ n = z)).card := by sorry
