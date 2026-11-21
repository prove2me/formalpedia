-- Prove2me | Theorems.Thm_Champernowne_sum_length_partial
-- name    : Champernowne.sum_length_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:37.584184+00:00
-- url     : https://prove2.me/theorems/54adc66a-f77f-410f-add8-e2d284387724
-- title:
--   Champernowne: sum length partial
-- statement:
--   Total digit length of a partial cohort.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L192-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L192-L202

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_length_partial {b : ℕ} (hb : 1 < b) (K t : ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    ∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length
      = t * (K + 1) := by sorry
