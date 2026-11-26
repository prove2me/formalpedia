-- Prove2me | Theorems.Thm_Erdos338Proof_pair_count
-- name    : Erdos338Proof.pair_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:01.323804+00:00
-- url     : https://prove2.me/theorems/b4ad8730-301c-5b43-8fd7-f4f32bffebdc
-- title:
--   Erdos338 Proof: pair count
-- statement:
--   Counting pairs: the `k ^ 2 - k` ordered pairs of distinct elements of `A ∩ [0, L)`, where
--   `k = |A ∩ [0, L)|`, have sums below `b ≥ 2 L`. A sum below `b` has at most `b` representations,
--   and fewer than `R` unless it lies in the set counted on the right.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L39-L85
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L39-L85

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.pair_count (A : Set ℕ) (R : ℕ) {b L : ℕ} (hL : 2 * L ≤ b) :
    cnt A L * cnt A L ≤ b * cnt {m | R ≤ #(rep A m)} b + b * R + cnt A L := by sorry
