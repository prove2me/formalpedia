-- Prove2me | Theorems.Thm_Champernowne_sum_length_cohort
-- name    : Champernowne.sum_length_cohort
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:52.679424+00:00
-- url     : https://prove2.me/theorems/13e08bdc-0c90-45a2-8c27-1cd279ff8e54
-- title:
--   Champernowne: sum length cohort
-- statement:
--   Total digit length of the `m`-digit cohort.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L180-L189
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L180-L189

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_length_cohort {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), (bigDigits b n).length
      = (b - 1) * b ^ (m - 1) * m := by sorry
