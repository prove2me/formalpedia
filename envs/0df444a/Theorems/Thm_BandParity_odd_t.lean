-- Prove2me | Theorems.Thm_BandParity_odd_t
-- name    : BandParity.odd_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:50.827731+00:00
-- url     : https://prove2.me/theorems/8fd16239-a6ce-4928-ab4c-51200844b4ec
-- title:
--   Band Parity: odd t
-- statement:
--   `t` is odd.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L67-L68
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L67-L68

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.odd_t (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) := by sorry
