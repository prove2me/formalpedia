-- Prove2me | Theorems.Thm_BandParity_sum_cls_neg
-- name    : BandParity.sum_cls_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:03.656792+00:00
-- url     : https://prove2.me/theorems/0f52af50-c0fc-4b7d-aa21-50b83c969633
-- title:
--   Band Parity: sum cls neg
-- statement:
--   For a function odd away from `0`, the class sums over `C_{-z}` and `C_z` are opposite.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L193-L207
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L193-L207

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hχ

theorem BandParity.sum_cls_neg (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = -g x)
    {z : GaussianInt} (hz : z ≠ 0) :
    ∑ x ∈ cls χ (-z), g x = -∑ x ∈ cls χ z, g x := by sorry
