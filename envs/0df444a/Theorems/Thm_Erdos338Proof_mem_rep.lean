-- Prove2me | Theorems.Thm_Erdos338Proof_mem_rep
-- name    : Erdos338Proof.mem_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:55.718321+00:00
-- url     : https://prove2.me/theorems/acb156fa-ba3d-4ba6-9c53-c2793257203c
-- title:
--   Erdos338 Proof: mem rep
-- statement:
--   The Erdos338 Proof construction uses the mem rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L27-L29
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Pairs.lean#L27-L29

module
public import Definitions.Def_Erdos338_Structure
public import Definitions.Def_Erdos338_Pairs
set_option autoImplicit true
@[expose] public section
public section
open Finset
open Erdos338Proof

theorem Erdos338Proof.mem_rep {A : Set ℕ} {m a : ℕ} :
    a ∈ rep A m ↔ a ≤ m ∧ a ∈ A ∧ m - a ∈ A ∧ 2 * a ≠ m := by sorry
