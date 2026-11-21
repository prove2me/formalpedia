-- Prove2me | Theorems.Thm_Champernowne_sum_countOccurrences_cohort_eq_head
-- name    : Champernowne.sum_countOccurrences_cohort_eq_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:14.881086+00:00
-- url     : https://prove2.me/theorems/bab61b06-fd0f-40fc-af36-7f83b366aa09
-- title:
--   Champernowne: sum count Occurrences cohort eq head
-- statement:
--   Split a cohort occurrence count into its head contribution and interior windows.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L519-L565
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/CountExtras.lean#L519-L565

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.sum_countOccurrences_cohort_eq_head {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), countOccurrences w (bigDigits b n)
      = ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
          (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by sorry
