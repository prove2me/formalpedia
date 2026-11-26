-- Prove2me | Theorems.Thm_Erdos338Proof_exists_rep_avoid
-- name    : Erdos338Proof.exists_rep_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:59:35.668699+00:00
-- url     : https://prove2.me/theorems/04c2e1dc-3f21-4439-bad8-270c47380e10
-- title:
--   Erdos338 Proof: exists rep avoid
-- statement:
--   If `m` has more than `2 |V|` representations, one of them avoids `V`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L135-L150
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L135-L150

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.exists_rep_avoid {A : Set ℕ} {m : ℕ} (V : Finset ℕ) (h : 2 * #V < #(rep A m)) :
    ∃ a ∈ rep A m, a ∉ V ∧ m - a ∉ V := by sorry
