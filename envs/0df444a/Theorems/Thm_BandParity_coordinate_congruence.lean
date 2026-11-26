-- Prove2me | Theorems.Thm_BandParity_coordinate_congruence
-- name    : BandParity.coordinate_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:26.932893+00:00
-- url     : https://prove2.me/theorems/8777ee02-9754-4a40-885d-7741e5e398fd
-- title:
--   Band Parity: coordinate congruence
-- statement:
--   **Coordinate Congruence.** `κ ≡ Q + k + t (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L106-L108
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L106-L108

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

theorem BandParity.coordinate_congruence (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] := by sorry
