-- Prove2me | Theorems.Thm_Erdos338Proof_pairs_dense
-- name    : Erdos338Proof.pairs_dense
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:26.648959+00:00
-- url     : https://prove2.me/theorems/e2f31aff-a202-4769-8c12-829bf13664d8
-- title:
--   Erdos338 Proof: pairs dense
-- statement:
--   If `δ b ≤ |A ∩ [0, b)|` for all large `b`, then for every `R` the set of numbers with at least
--   `R` representations as a sum of two distinct elements of `A` satisfies the same with `δ ^ 2 / 8` in
--   place of `δ`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L90-L132
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L90-L132

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.pairs_dense {δ : ℝ} (hδ : 0 < δ) {A : Set ℕ} {N₀ : ℕ}
    (hN₀ : ∀ b ≥ N₀, δ * b ≤ cnt A b) (R : ℕ) :
    ∃ N, ∀ b ≥ N, δ ^ 2 / 8 * b ≤ cnt {m | R ≤ #(rep A m)} b := by sorry
