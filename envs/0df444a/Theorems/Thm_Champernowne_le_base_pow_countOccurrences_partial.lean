-- Prove2me | Theorems.Thm_Champernowne_le_base_pow_countOccurrences_partial
-- name    : Champernowne.le_base_pow_countOccurrences_partial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:36:41.799395+00:00
-- url     : https://prove2.me/theorems/cb2ba96d-963f-49d9-991e-2777881b7376
-- title:
--   Champernowne: le base pow count Occurrences partial
-- statement:
--   Partial-cohort comparison, lower.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L376-L449
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L376-L449

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.le_base_pow_countOccurrences_partial {b : ℕ} (hb : 1 < b) (K t : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), (bigDigits b n).length)
      ≤ b ^ w.length * (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 3 * (w.length + 1) * b ^ (K + 1) := by sorry
