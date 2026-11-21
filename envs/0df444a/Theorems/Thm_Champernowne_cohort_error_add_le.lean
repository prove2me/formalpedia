-- Prove2me | Theorems.Thm_Champernowne_cohort_error_add_le
-- name    : Champernowne.cohort_error_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:45.103188+00:00
-- url     : https://prove2.me/theorems/bc625f9c-4df3-4912-b9d9-e1bc55524905
-- title:
--   Champernowne: cohort error add le
-- statement:
--   The accumulated cohort error is absorbed by the next power of the base.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L452-L456
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L452-L456

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.cohort_error_add_le {b : ℕ} (hb : 1 < b) (c K : ℕ) :
    6 * c * b ^ K + 3 * c * b ^ (K + 1) ≤ 6 * c * b ^ (K + 1) := by sorry
