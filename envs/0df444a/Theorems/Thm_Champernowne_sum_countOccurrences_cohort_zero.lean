-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_cohort_zero
-- name    : Champernowne.sum_countOccurrences_cohort_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:32.42695+00:00
-- url     : https://prove2.me/theorems/e269927b-9bad-4c1d-967b-0dfd6bc3d906
-- title:
--   Champernowne: sum count Occurrences cohort zero
-- statement:
--   Block `w` with head `0` occurs `(m-k)·(b-1)·b^(m-k-1)` times inside the
--   digit strings of all `m`-digit numbers.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L582-L589
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L582-L589

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_countOccurrences_cohort_zero {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by sorry
