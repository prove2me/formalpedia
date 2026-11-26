-- Prove2me | Theorems.Thm_Erdos338Proof_exists_mem_Ioc
-- name    : Erdos338Proof.exists_mem_Ioc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:58:49.197655+00:00
-- url     : https://prove2.me/theorems/56b044ab-2021-4ab0-b06e-492be88d7fde
-- title:
--   Erdos338 Proof: exists mem Ioc
-- statement:
--   A set `E` with `γ b ≤ |E ∩ [0, b)|` for all large `b` has an element in `(y, C y]` for all
--   large `y`, once `2 / γ ≤ C`.
--
--   Source: https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L136-L157
-- source:
--   https://github.com/veljjanoski/erdos338-palomar/blob/a699263d0f7cdce0e5b3026bce86eab30973d0f8/Erdos338/Structure.lean#L136-L157

module
public import Definitions.Def_Erdos338_Covering
public import Definitions.Def_Erdos338_Structure
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped Pointwise
open Erdos338Proof

theorem Erdos338Proof.exists_mem_Ioc {γ : ℝ} (hγ : 0 < γ) {C : ℕ} (hC : (2 / γ : ℝ) ≤ C) {E : Set ℕ} {N : ℕ}
    (hN : ∀ b ≥ N, γ * b ≤ cnt E b) {y : ℕ} (hyN : N ≤ y) (hy2 : 2 ≤ y) :
    ∃ ℓ ∈ E, y < ℓ ∧ ℓ ≤ C * y := by sorry
