-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_cohort
-- name    : Champernowne.sum_countOccurrences_cohort
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:33.293683+00:00
-- url     : https://prove2.me/theorems/b99db466-1ec6-4f5d-a8e4-eb335ae14150
-- title:
--   Champernowne: sum count Occurrences cohort
-- statement:
--   Block `w` with nonzero head occurs
--   `b^(m-k) + (m-k)·(b-1)·b^(m-k-1)` times inside the digit strings of all
--   `m`-digit numbers (`k := w.length`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L570-L578
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L570-L578

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_countOccurrences_cohort {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? ≠ some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = b ^ (m - w.length)
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by sorry
