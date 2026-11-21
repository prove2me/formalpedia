-- Prove2me | Theorems.Thm_Champernowne_length_champBlocks
-- name    : Champernowne.length_champBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:37.510358+00:00
-- url     : https://prove2.me/theorems/37eff000-e052-4238-8936-df4f60354773
-- title:
--   Champernowne: length champ Blocks
-- statement:
--   The stream-prefix length as a sum over the numbers `1..N`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L170-L177
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L170-L177

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.length_champBlocks (b N : ℕ) :
    (champBlocks b N).length
      = ∑ n ∈ Finset.Ico 1 (N + 1), (bigDigits b n).length := by sorry
