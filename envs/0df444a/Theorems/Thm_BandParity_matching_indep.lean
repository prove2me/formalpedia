-- Prove2me | Theorems.Thm_BandParity_matching_indep
-- name    : BandParity.matching_indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:11:44.40504+00:00
-- url     : https://prove2.me/theorems/aeebe5fa-e607-4ed4-81fb-b914b5c6a2b7
-- title:
--   Band Parity: matching indep
-- statement:
--   **Independence of the matching.**
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L31-L35
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L31-L35

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem BandParity.matching_indep {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] := by sorry
