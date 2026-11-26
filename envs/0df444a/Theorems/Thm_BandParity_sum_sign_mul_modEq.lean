-- Prove2me | Theorems.Thm_BandParity_sum_sign_mul_modEq
-- name    : BandParity.sum_sign_mul_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:42.184569+00:00
-- url     : https://prove2.me/theorems/ded56e33-540a-54c3-8502-bf1f82a16e36
-- title:
--   Band Parity: sum sign mul mod Eq
-- statement:
--   Termwise form: a sum of products of signs is congruent to the sum of the two marginals
--   minus the number of terms.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L32-L43
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Matching.lean#L32-L43

module
public import Mathlib
public import Definitions.Def_BandParity_Matching
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem BandParity.sum_sign_mul_modEq {ι : Type*} (X : Finset ι) (σ τ : ι → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ x ∈ X, τ x = 1 ∨ τ x = -1) :
    ∑ x ∈ X, σ x * τ x ≡ ∑ x ∈ X, σ x + ∑ x ∈ X, τ x - X.card [ZMOD 4] := by sorry
