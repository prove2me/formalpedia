-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_Ico_eq
-- name    : Champernowne.sum_countOccurrences_Ico_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:38:04.291942+00:00
-- url     : https://prove2.me/theorems/115a1e96-7575-4a9e-aa82-efa186f5db2e
-- title:
--   Champernowne: sum count Occurrences Ico eq
-- statement:
--   Partial-cohort occurrence sum as a sum of per-position cards.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L298-L318
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/DigitCount.lean#L298-L318

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_countOccurrences_Ico_eq {b : ℕ} (hb : 1 < b) (K t : ℕ) (w : List ℕ)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
      = ∑ j ∈ Finset.range (K + 2),
          ((Finset.Ico (b ^ K) (b ^ K + t)).filter
            (fun n => ((bigDigits b n).drop j).take w.length = w)).card := by sorry
