-- Prove2me | Theorems.Thm_Erdos338Proof_dense_step
-- name    : Erdos338Proof.dense_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:36.217999+00:00
-- url     : https://prove2.me/theorems/f5be35ab-76c5-5767-8df6-b667eda6302c
-- title:
--   Erdos338 Proof: dense step
-- statement:
--   One dense step: for a large `ℓ ∈ E`, every `x` with `h ℓ ≤ x` and `x + h ℓ ≤ m ℓ` is a sum
--   of `m` elements of `E`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L37-L132
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L37-L132

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof

theorem Erdos338Proof.dense_step {γ : ℝ} (hγ : 0 < γ) {h : ℕ} (hh : (4 / γ : ℝ) < h) {E : Set ℕ}
    {F : Finset ℕ} (hFE : (F : Set ℕ) ⊆ E)
    (h1 : (1 : ℤ) ∈ Submodule.span ℤ ((Nat.cast : ℕ → ℤ) '' F)) {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) (hE0 : 0 ∈ E) {ℓ : ℕ} (hℓE : ℓ ∈ E)
    (hℓN : N ≤ ℓ) (hℓF : F.sup id ≤ ℓ) (hℓγ : (2 / γ : ℝ) ≤ ℓ) {m x : ℕ}
    (hx1 : h * ℓ ≤ x) (hx2 : x + h * ℓ ≤ m * ℓ) :
    ∃ M : Multiset ℕ, M.card = m ∧ (∀ a ∈ M, a ∈ E) ∧ M.sum = x := by sorry
