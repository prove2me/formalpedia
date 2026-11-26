-- Prove2me | Theorems.Thm_BandParity_p_dvd_cosetSum
-- name    : BandParity.p_dvd_cosetSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:17.907549+00:00
-- url     : https://prove2.me/theorems/34ad19ac-1002-4567-8e43-1b6ee6b7e4fa
-- title:
--   Band Parity: p dvd coset Sum
-- statement:
--   **Proposition 3.1 (integrality).** `p ∣ ∑_{n ∈ C_z} n`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L79-L83
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L79-L83

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

theorem BandParity.p_dvd_cosetSum (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) ∣ cosetSum χ z := by sorry
