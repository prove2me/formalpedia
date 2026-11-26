-- Prove2me | Theorems.Thm_BandParity_T_eq
-- name    : BandParity.T_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:19.661559+00:00
-- url     : https://prove2.me/theorems/c920ffd9-6318-5176-bcec-6b6a0e4eecdd
-- title:
--   Band Parity: T eq
-- statement:
--   `∑ χ(n) n = p (k + i t)`, i.e. `B_{1,χ} = k + i t`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L59-L60
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L59-L60

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

theorem BandParity.T_eq (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) := by sorry
