-- Prove2me | Theorems.Thm_BandParity_sum_eq_two_nsmul_half
-- name    : BandParity.sum_eq_two_nsmul_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:25.6328+00:00
-- url     : https://prove2.me/theorems/e3ae6a0c-86a7-5c75-9e7a-143cece5f371
-- title:
--   Band Parity: sum eq two nsmul half
-- statement:
--   An even function vanishing at `0` sums to twice its sum over `0 ≤ ⟨x⟩ < p/2`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L90-L107
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L90-L107

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

theorem BandParity.sum_eq_two_nsmul_half {R : Type*} [AddCommMonoid R] (hp2 : p ≠ 2) (h : ZMod p → R)
    (h0 : h 0 = 0) (hsym : ∀ x, h (-x) = h x) :
    ∑ x, h x = 2 • ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x := by sorry
