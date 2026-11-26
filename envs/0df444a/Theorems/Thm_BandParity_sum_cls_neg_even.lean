-- Prove2me | Theorems.Thm_BandParity_sum_cls_neg_even
-- name    : BandParity.sum_cls_neg_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:44.128055+00:00
-- url     : https://prove2.me/theorems/3497a3d0-7646-46a0-a6f7-bfd4fe87378b
-- title:
--   Band Parity: sum cls neg even
-- statement:
--   For a function even away from `0`, the class sums over `C_{-z}` and `C_z` agree.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L211-L225
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L211-L225

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

theorem BandParity.sum_cls_neg_even (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = g x)
    {z : GaussianInt} (hz : z ≠ 0) :
    ∑ x ∈ cls χ (-z), g x = ∑ x ∈ cls χ z, g x := by sorry
