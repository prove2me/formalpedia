-- Prove2me | Theorems.Thm_BandParity_matching
-- name    : BandParity.matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:11:00.122608+00:00
-- url     : https://prove2.me/theorems/74ee4ad8-4807-56f7-aa71-cb5ef2f57ddd
-- title:
--   Band Parity: matching
-- statement:
--   **The matching lemma.** For a bijection `π` from `X` onto `Y` and sign functions `σ` on `X`
--   and `τ` on `Y`, `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - |X| (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L24-L28
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L24-L28

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset

theorem BandParity.matching {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] := by sorry
