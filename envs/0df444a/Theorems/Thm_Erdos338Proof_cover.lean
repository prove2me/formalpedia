-- Prove2me | Theorems.Thm_Erdos338Proof_cover
-- name    : Erdos338Proof.cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:52.979415+00:00
-- url     : https://prove2.me/theorems/9e6f8db4-da27-512a-8a11-b2e2ecd9d026
-- title:
--   Erdos338 Proof: cover
-- statement:
--   **Covering**: for `γ > 0` there is `K` such that every `E ⊆ ℕ` containing `0`, whose elements
--   generate `ℤ`, and with `γ b ≤ |E ∩ [0, b)|` for all large `b`, contains every large integer as a
--   sum of exactly `K` elements.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L162-L202
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L162-L202

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof

theorem Erdos338Proof.cover {γ : ℝ} (hγ : 0 < γ) : ∃ K : ℕ, (2 / γ : ℝ) < K ∧ ∀ E : Set ℕ, 0 ∈ E →
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ E ∧ (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) →
    (∃ N, ∀ b ≥ N, γ * b ≤ cnt E b) →
    ∃ N', ∀ x ≥ N', ∃ M : Multiset ℕ, M.card = K ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by sorry
