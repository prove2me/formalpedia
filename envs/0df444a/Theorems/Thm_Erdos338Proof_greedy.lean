-- Prove2me | Theorems.Thm_Erdos338Proof_greedy
-- name    : Erdos338Proof.greedy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:40.568865+00:00
-- url     : https://prove2.me/theorems/3f602576-b6e2-4ab6-b47d-29adec1289a5
-- title:
--   Erdos338 Proof: greedy
-- statement:
--   **Greedy step**: if every element of `Ms` has more than `2 (|U| + 2 |Ms|)` representations,
--   then the sum of `Ms` is a sum of `2 |Ms|` distinct elements of `A`, none of them in `U`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L154-L187
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L154-L187

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.greedy (A : Set ℕ) (U : Finset ℕ) (Ms : Multiset ℕ)
    (hMs : ∀ m ∈ Ms, 2 * (#U + 2 * Multiset.card Ms) < #(rep A m)) :
    ∃ S : Finset ℕ, Disjoint U S ∧ (∀ x ∈ S, x ∈ A) ∧ #S = 2 * Multiset.card Ms ∧
      ∑ x ∈ S, x = Ms.sum := by sorry
