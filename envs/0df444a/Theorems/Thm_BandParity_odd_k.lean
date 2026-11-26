-- Prove2me | Theorems.Thm_BandParity_odd_k
-- name    : BandParity.odd_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:42.309696+00:00
-- url     : https://prove2.me/theorems/f33e0bf5-fe57-47db-a084-2edac2f26ce3
-- title:
--   Band Parity: odd k
-- statement:
--   `k` is odd.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L63-L64
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L63-L64

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

theorem BandParity.odd_k (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) := by sorry
