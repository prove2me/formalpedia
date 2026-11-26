-- Prove2me | Theorems.Thm_BandParity_class_sum_zmod
-- name    : BandParity.class_sum_zmod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:11.04439+00:00
-- url     : https://prove2.me/theorems/14bb21e6-01b0-5414-b4f0-f10ad216421d
-- title:
--   Band Parity: class sum zmod
-- statement:
--   The sum of a class in `ZMod p` vanishes (multiplication by a kernel element permutes it).
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L67-L76
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L67-L76

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

theorem BandParity.class_sum_zmod (hp5 : 5 < p) (z : GaussianInt) :
    ∑ n : ZMod p, (if χ n = z then n else 0) = 0 := by sorry
