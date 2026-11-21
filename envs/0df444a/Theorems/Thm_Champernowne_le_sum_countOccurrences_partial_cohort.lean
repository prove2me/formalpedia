-- Prove2me | Theorems.Thm_Champernowne_le_sum_countOccurrences_partial_cohort
-- name    : Champernowne.le_sum_countOccurrences_partial_cohort
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:06.329196+00:00
-- url     : https://prove2.me/theorems/7d683bb5-c531-43b6-875a-baf28d5f9fd4
-- title:
--   Champernowne: le sum count Occurrences partial cohort
-- statement:
--   Partial-cohort occurrence sum, lower bound (stated additively; drops the
--   head position, which is only ever a nonnegative contribution).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L322-L359
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L322-L359

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_sum_countOccurrences_partial_cohort {b : ℕ} (hb : 1 < b) (K t : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (K + 1 - w.length) * (t / b ^ w.length)
      ≤ (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 2 * b ^ (K + 1 - w.length) := by sorry
