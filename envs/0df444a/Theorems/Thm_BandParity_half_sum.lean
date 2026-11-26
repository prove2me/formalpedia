-- Prove2me | Theorems.Thm_BandParity_half_sum
-- name    : BandParity.half_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:45.502495+00:00
-- url     : https://prove2.me/theorems/24c241d5-9e47-47ce-9790-56cd5e0cd126
-- title:
--   Band Parity: half sum
-- statement:
--   **The half-range sum** (the case `m = 1`, `N = p`, `r = 2` of SUZ (6), conjugated form).
--   For an odd character, `p · χ(2) · ∑_{0 < n < p/2} χ(n) = (1 - 2 χ(2)) · T χ`, i.e.
--   `∑_{0<n<p/2} χ(n) = (χ̄(2) - 2) B₁,χ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L73-L116
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/FixedBase.lean#L73-L116

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem BandParity.half_sum (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hodd : χ (-1) = -1) :
    (p : R) * χ 2 * ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n =
      (1 - 2 * χ 2) * T χ := by sorry
