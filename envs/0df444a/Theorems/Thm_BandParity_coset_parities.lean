-- Prove2me | Theorems.Thm_BandParity_coset_parities
-- name    : BandParity.coset_parities
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:07.83987+00:00
-- url     : https://prove2.me/theorems/69135636-b8d8-438e-84fe-ee9596ce87af
-- title:
--   Band Parity: coset parities
-- statement:
--   **Exact coset parities.** `∑_{u ∈ H} s(u) = k + 2t` and `∑_{u ∈ 2H} s(u) = t - 2k`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L96-L98
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L96-L98

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

theorem BandParity.coset_parities (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ := by sorry
