-- Prove2me | Theorems.Thm_BandParity_sum_alt_half
-- name    : BandParity.sum_alt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:17.980803+00:00
-- url     : https://prove2.me/theorems/46d342c9-fbfd-42e1-8027-17cb022c52d1
-- title:
--   Band Parity: sum alt half
-- statement:
--   `∑_{0 < v < p/2} (-1)^v = 0` when `p ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L148-L154
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L148-L154

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
omit hp

theorem BandParity.sum_alt_half (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v = 0 := by sorry
