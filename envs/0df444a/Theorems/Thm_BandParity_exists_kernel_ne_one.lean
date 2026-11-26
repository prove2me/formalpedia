-- Prove2me | Theorems.Thm_BandParity_exists_kernel_ne_one
-- name    : BandParity.exists_kernel_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:58.756516+00:00
-- url     : https://prove2.me/theorems/e8005c5a-668f-5496-94c9-4a2f6563e6d3
-- title:
--   Band Parity: exists kernel ne one
-- statement:
--   A nontrivial element of the kernel, when `p > 5`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L57-L64
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L57-L64

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

theorem BandParity.exists_kernel_ne_one (hp5 : 5 < p) : ∃ a : ZMod p, a ≠ 0 ∧ a ≠ 1 ∧ χ a = 1 := by sorry
