-- Prove2me | Theorems.Thm_Egrs75_LeafInduction_seed_lt_pow_succ
-- name    : Egrs75.LeafInduction.seed_lt_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:46.096064+00:00
-- url     : https://prove2.me/theorems/f8225a05-4ffd-4ffc-94e0-9619662c0b6c
-- title:
--   Leaf Induction: seed lt pow succ
-- statement:
--   `N < p^(N+1)` for `p ≥ 2`, via `N < 2^N ≤ 2^(N+1) ≤ p^(N+1)`.  KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L110-L114
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L110-L114

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.LeafInduction
open Nat
open Egrs75

theorem Egrs75.LeafInduction.seed_lt_pow_succ {p : ℕ} (hp : 2 ≤ p) (N : ℕ) : N < p ^ (N + 1) := by sorry
