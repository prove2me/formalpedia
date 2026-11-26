-- Prove2me | Theorems.Thm_Erdos338Proof_restricted_of_density
-- name    : Erdos338Proof.restricted_of_density
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:32.92762+00:00
-- url     : https://prove2.me/theorems/a605a159-3730-545c-8a30-e11cd69bdb25
-- title:
--   Erdos338 Proof: restricted of density
-- statement:
--   The Erdos338 Proof construction uses the restricted of density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L31-L64
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Main.lean#L31-L64

module
public import Definitions.Def_Erdos338_Pairs
public import Definitions.Def_Erdos338_Residue
public import Definitions.Def_Erdos338_Shift
public import Definitions.Def_Erdos338_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos338Proof

theorem Erdos338Proof.restricted_of_density (A : Set ℕ)
    (hres : ∀ Q, 0 < Q → ∀ c, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ ∑ x ∈ S, x ≡ c [MOD Q])
    {δ : ℝ} (hδ : 0 < δ) {N₀ : ℕ} (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) :
    ∃ t, ∀ᶠ n in Filter.atTop, ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ #S ≤ t ∧ ∑ x ∈ S, x = n := by sorry
