-- Prove2me | Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits
-- name    : Egrs75.LeafInduction.badCountQ_eq_zero_iff_lowDigits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:35.614859+00:00
-- url     : https://prove2.me/theorems/3ae3c14a-c60f-45c9-9fa8-4487ece38269
-- title:
--   Leaf Induction: bad Count Q eq zero iff low Digits
-- statement:
--   **Base case of the induction (KERNEL-CLEAN).**  The potential vanishes exactly
--   when every base-`q` digit is `≤ (q-1)/2`, i.e. when `n` is `LowDigits q`.  So a
--   number with potential `0` is already low in base `q`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L133-L136
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/LeafInduction.lean#L133-L136

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

theorem Egrs75.LeafInduction.badCountQ_eq_zero_iff_lowDigits {q n : ℕ} :
    badCountQ q n = 0 ↔ LowDigits q n := by sorry
